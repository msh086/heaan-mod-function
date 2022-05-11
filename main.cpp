#include <iostream>
#include <HEAAN.h>

using namespace NTL;
using namespace heaan;
using std::cout, std::endl, std::complex;

/**
 *
 * @param scheme
 * @param ciphertext
 * @param coeffs from the lowest term to the highest term
 * @return
 */
Ciphertext homo_eval_poly(Scheme &scheme, const Ciphertext &ciphertext, const std::vector<double> &coeffs) {
    auto n_coeffs = coeffs.size();
    if (n_coeffs == 0)
        return ciphertext;
    if (n_coeffs == 1)
        throw std::invalid_argument("the polynomial to be evaluated should not be constant");
    auto max_deg = coeffs.size() - 1;
    auto tower_size = NTL::NumBits(max_deg);
    std::vector<Ciphertext> tower;
    tower.reserve(tower_size);
    tower.emplace_back(ciphertext);
    auto log_factor = ciphertext.logp;
    for (long i = 1; i < tower_size; i++) {
        Ciphertext tmp;
        scheme.square(tmp, tower[i - 1]);
        scheme.reScaleByAndEqual(tmp, log_factor);
        tower.emplace_back(tmp);
    }
    // c^(2^0), ..., c^(2^(tower_size - 1)) are computed
    Ciphertext dst = ciphertext;
    scheme.multByConstAndEqual(dst, coeffs[1], log_factor);
    scheme.reScaleByAndEqual(dst, log_factor);
    scheme.addConstAndEqual(dst, coeffs[0], log_factor);
    // now dst = a_0 + a_1 * x
    for (int deg = 2; deg < n_coeffs; deg++) {
        unsigned int cur_deg_total_bits = NTL::NumBits(deg), cursor_bit_idx = 0;
        for (; cursor_bit_idx < cur_deg_total_bits; cursor_bit_idx++) {
            if ((1 << cursor_bit_idx) & deg)
                break;
        }

        if (fabs(coeffs[deg]) * exp2(tower[cursor_bit_idx].logp) < 0.5) // too small s.t. encoding results is zero poly
            continue;

        Ciphertext tmp_ciphertext = tower[cursor_bit_idx];
        scheme.multByConstAndEqual(tmp_ciphertext, coeffs[deg], log_factor);
        scheme.reScaleByAndEqual(tmp_ciphertext, log_factor);
        // FIXME: use moddownto instead?
        while (++cursor_bit_idx < cur_deg_total_bits) {
            if ((1 << cursor_bit_idx) & deg) {
                scheme.multAndEqual(tmp_ciphertext, tower[cursor_bit_idx]);
                scheme.reScaleByAndEqual(tmp_ciphertext, log_factor);
            } else {
                scheme.multByConstAndEqual(tmp_ciphertext, 1, log_factor);
                scheme.reScaleByAndEqual(tmp_ciphertext, log_factor);
            }
        }
        while (dst.logq > tmp_ciphertext.logq) {
            scheme.multByConstAndEqual(dst, 1, log_factor);
            scheme.reScaleByAndEqual(dst, log_factor);
        }
        scheme.addAndEqual(dst, tmp_ciphertext);
    }
    return dst; // will RVO or NRVO optimize this out?
}

void plain_eval_poly(complex<double> *dst, const complex<double> *src, int len, const std::vector<double> &coeffs) {
    for (int i = 0; i < len; i++) {
        auto src_i = src[i]; // handle the case when dst == src
        dst[i] = 0;
        for (int j = 0; j < coeffs.size(); j++) {
            dst[i] += coeffs[j] * pow(src_i, j);
        }
    }
}

Ciphertext homo_eval_mod(Scheme &scheme, Ciphertext &ciphertext, int n_iter, int K, double modulus) {
    std::vector<double> coeffs{0, 4.47839789092541, 0, -22.391989454627, 0, 94.0463557094336, 0, -291.095862910151, 0,
                               679.223680123687, 0, -1222.60262422264, 0, 1724.18318800628, 0, -1921.232695207, 0,
                               1695.20531930029, 0, -1179.70428653061, 0, 640.410898402333, 0, -265.783179178834, 0,
                               81.5068416148424, 0, -17.4159917980433, 0, 2.3164127022028, 0, -0.144464448094368};
//    std::vector<double> coeffs{1, 1};
    Ciphertext res = ciphertext;
    bool init = false;
    double range = K * modulus + modulus * 0.5;
    auto logp = ciphertext.logp;
    for (int i = 1; i <= K; i++) {
        // Step 1. adjust the inputs
        // formula: sgn{(2k+1)/(4k-2(i-1))[x/range+(2k-1-2(i-1))/(2k+1)]}
        //         =(2k+1)/[(4k-2(i-1))*range]x + (2k-1-2(i-1))/(4k-2(i-1)) denote as a*x +- b
        double a = (2 * K + 1) / (range * (4 * K - 2 * (i - 1)));
        double b = double(2 * K - 1 - 2 * (i - 1)) / (4 * K - 2 * (i - 1));
        for (int s = 0; s <= 1; s++) { // s == 0 mean ax+b, s == 1 means ax-b
            Ciphertext tmp;
            scheme.multByConst(tmp, ciphertext, a, logp);
            scheme.reScaleByAndEqual(tmp, logp);
            scheme.addConstAndEqual(tmp, s ? -b : b, logp);
            // Step 2. composition of sign function
            for (int j = 0; j < n_iter; j++) {
                // NOTE: no operator= for Ciphertext, so `tmp = homo_eval_poly(...)` will cause SIGSEGV
                auto iterated = homo_eval_poly(scheme, tmp, coeffs);
                tmp.copy(iterated);
            }
            // Step 3. place the sign functions together
            if (!init) {
                res.copy(tmp); // NOTE: use copy here too!
                init = true;
            } else
                scheme.addAndEqual(res, tmp);
        }
    }
    // Step 4. Multiply by q/2
    scheme.multByConstAndEqual(res, modulus / 2, logp);
    scheme.reScaleByAndEqual(res, logp);
    return res;
}

void plain_eval_mod(complex<double>* dst, const complex<double>* src, int len, int n_iter, int K, double modulus){
    std::vector<double> coeffs{0, 4.47839789092541, 0, -22.391989454627, 0, 94.0463557094336, 0, -291.095862910151, 0,
                               679.223680123687, 0, -1222.60262422264, 0, 1724.18318800628, 0, -1921.232695207, 0,
                               1695.20531930029, 0, -1179.70428653061, 0, 640.410898402333, 0, -265.783179178834, 0,
                               81.5068416148424, 0, -17.4159917980433, 0, 2.3164127022028, 0, -0.144464448094368};
    std::vector<complex<double>> scratch(len);
    double range = K * modulus + modulus * 0.5;
    for (int i = 1; i <= K; i++) {
        // Step 1. adjust the inputs
        // formula: sgn{(2k+1)/(4k-2(i-1))[x/range+(2k-1-2(i-1))/(2k+1)]}
        //         =(2k+1)/[(4k-2(i-1))*range]x + (2k-1-2(i-1))/(4k-2(i-1)) denote as a*x +- b
        double a = (2 * K + 1) / (range * (4 * K - 2 * (i - 1)));
        double b = double(2 * K - 1 - 2 * (i - 1)) / (4 * K - 2 * (i - 1));
        for (int s = 0; s <= 1; s++) { // s == 0 mean ax+b, s == 1 means ax-b
            plain_eval_poly(scratch.data(), src, len, {s ? -b : b, a});
            // Step 2. composition of sign function
            for (int j = 0; j < n_iter; j++)
                plain_eval_poly(scratch.data(), scratch.data(), len, coeffs);
            // Step 3. place the sign functions together
            for(int j = 0; j < len; j++)
                dst[i] += scratch[i];
        }
    }
    // Step 4. Multiply by q/2
    for(int i = 0; i < len; i++)
        dst[i] *= modulus / 2;
}


// taylor approx in [-1/T, 1/T]
void testBootstrap(long logq, long logp, long logSlots, long logT) {
    cout << "!!! START TEST BOOTSTRAP !!!" << endl;

    srand(time(nullptr));
    SetNumThreads(8);
    TimeUtils timeutils;
    Ring ring;
    SecretKey secretKey(ring);
    Scheme scheme(secretKey, ring);

    timeutils.start("Key generating");
    scheme.addBootKey(secretKey, logSlots, logq + 4);
    timeutils.stop("Key generated");

    long slots = (1 << logSlots);
    complex<double> *mvec = EvaluatorUtils::randomComplexArray(slots);

    Ciphertext cipher;
    scheme.encrypt(cipher, mvec, slots, logp, logq);

    // FIXME: debugging
    int n_iter = 3, K = 1;
    double modulus = 0.1, ratio = pow(2, -1), radius = modulus * ratio;

    std::vector<complex<double>> mod_input(slots);
    // sample uniformly from Union_i={-K, -K+1,..., K}(i*modulus + (-radius, radius))
    for(auto & e : mod_input){
        // sample double in (-radius, radius)
        auto rand_l = NTL::RandomBits_ulong(64);
        double bias = long(rand_l) / std::pow(2, 63) * radius;
        // sample nK in [-K, K]
        rand_l = (NTL::RandomBits_long(NumBits(2 * K + 1)) % (2 * K + 1));
        e.real((long(rand_l) - K) * modulus + bias);
    }
    Ciphertext dbg;
    scheme.encrypt(dbg, mod_input.data(), slots, logp, 800); // NOTE: use larger value here, logq is too small

//    scheme.conjugate(dbg, cipher0);
//    scheme.addAndEqual(dbg, cipher0);
//    scheme.multByConstAndEqual(dbg, 0.5, logp);
//    scheme.reScaleByAndEqual(dbg, logp);

    // messages in slots have bound of 1, so 3 * 0.4 is enough
    auto dbg_res = homo_eval_mod(scheme, dbg, n_iter, K, modulus);
    auto dbg_vec = scheme.decrypt(secretKey, dbg_res);

    std::vector<double> mod_coeffs{0, 4.47839789092541, 0, -22.391989454627, 0, 94.0463557094336, 0, -291.095862910151, 0,
                                   679.223680123687, 0, -1222.60262422264, 0, 1724.18318800628, 0, -1921.232695207, 0,
                                   1695.20531930029, 0, -1179.70428653061, 0, 640.410898402333, 0, -265.783179178834, 0,
                                   81.5068416148424, 0, -17.4159917980433, 0, 2.3164127022028, 0, -0.144464448094368};
    std::vector<complex<double>> plain_eval_vec(slots);
    plain_eval_mod(plain_eval_vec.data(), mod_input.data(), slots, n_iter, K, modulus);

    for (int i = 0; i < slots; i++) {
        cout << "input[" << i << "]= " << mod_input[i] << '\n';
        cout << "homo_mod[" << i << "] = " << dbg_vec[i] << '\n';
        cout << "plain_mod[" << i << "] = " << plain_eval_vec[i] << '\n';
    }
    return;

    // FIXME: end debugging

    cout << "cipher logq before: " << cipher.logq << endl;

    scheme.modDownToAndEqual(cipher, logq);
    scheme.normalizeAndEqual(cipher);
    cipher.logq = logQ;
    cipher.logp = logq + 4;

    Ciphertext rot;
    timeutils.start("SubSum");
    for (long i = logSlots; i < logNh; ++i) {
        scheme.leftRotateFast(rot, cipher, (1 << i));
        scheme.addAndEqual(cipher, rot);
    }
    scheme.divByPo2AndEqual(cipher, logNh);
    timeutils.stop("SubSum");

    // FIXME: debug
    Plaintext before_c2s;
    scheme.decryptMsg(before_c2s, secretKey, cipher);

    timeutils.start("CoeffToSlot");
    scheme.coeffToSlotAndEqual(cipher);
    timeutils.stop("CoeffToSlot");

    // FIXME: debug
    Plaintext before_mod;
    scheme.decryptMsg(before_mod, secretKey, cipher);
    before_mod.n = Nh; // number of total slots is N/2
    auto before_mod_slots = scheme.decode(before_mod);
//    // confirm the effect of CoeffToSlot
//    auto before_mod_q = ring.qpows[before_mod.logq];
//    for(int i = 0; i < N; i++){
//        auto expected = before_c2s.mx[i];
//        rem(expected, expected, before_mod_q);
//        if (NumBits(expected) == before_mod.logq) expected -= before_mod_q;
//
//        auto got = before_mod_slots[i];
//        std::cout << "i th coeff: " << expected << " ==> " << got << '\n';
//    }


    timeutils.start("EvalExp");
    scheme.evalExpAndEqual(cipher, logT);
    timeutils.stop("EvalExp");

    // FIXME: debug
    Plaintext after_mod;
    scheme.decryptMsg(after_mod, secretKey, cipher);
    after_mod.n = Nh;
    auto after_mod_slots = scheme.decode(after_mod);
    for (int i = 0; i < Nh; i++) {
        std::cout << "i th slot: " << before_mod_slots[i] << " ==> " << after_mod_slots[i] << '\n';
    }

    timeutils.start("SlotToCoeff");
    scheme.slotToCoeffAndEqual(cipher);
    timeutils.stop("SlotToCoeff");

    cipher.logp = logp;
    cout << "cipher logq after: " << cipher.logq << endl;

    complex<double> *dvec = scheme.decrypt(secretKey, cipher);

    StringUtils::compare(mvec, dvec, slots, "boot");

    cout << "!!! END TEST BOOTSRTAP !!!" << endl;
}

int main() {
    /*
  * Basic Parameters are in src/Params.h
  * If you want to use another parameter, you need to change src/Params.h file and re-complie this library.
  */

    // Parameters //
    long logq = 40; ///< Ciphertext modulus (this value should be <= logQ in "scr/Params.h")
    long logp = 30; ///< Scaling Factor (larger logp will give you more accurate value)
    long logn = 3; ///< number of slot is 1024 (this value should be < logN in "src/Params.h")
    long n = 1 << logn;
    long slots = n;

    long logT = 4;
    /**
     * 	long logq = 800; ///< Ciphertext Modulus
	 *  long logp = 30; ///< Real message will be quantized by multiplying 2^40
	 *  long logn = 4; ///< log2(The number of slots)
     */

    testBootstrap(logq, logp, logn, logT);
}
