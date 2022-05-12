#include <iostream>
#include <cmath>
#include <thread>
#include <map>
#include <HEAAN.h>

using namespace NTL;
using namespace heaan;
using std::cout, std::endl, std::complex;

const static std::map<int, std::vector<double>> coeff_map{
        {
                15, {0, 3.14208984375,     0, -7.33154296875,      0, 13.19677734375,    0, -15.71044921875,
                                                                                                                 0, 12.21923828125,     0, -5.99853515625,      0, 1.69189453125,      0, -0.20947265625}
        },
        {
                31, {0, 4.478397890925407, 0, -22.391989454627037, 0, 94.04635570943356, 0, -291.0958629101515,  0,
                                                                                                                    679.2236801236868,  0, -1222.6026242226362, 0, 1724.1831880062819, 0, -1921.2326952069998, 0,
                            1695.205319300294, 0, -1179.704286530614, 0, 640.4108984023333,  0, -265.78317917883396, 0,
                            81.50684161484241, 0, -17.41599179804325,  0, 2.316412702202797,  0, -0.14446444809436798}
        },
        {
                63, {0, 6.358192239869881, 0, -65.70131981198877,  0, 591.311878307899,  0, -4082.8677311735883, 0,
                                                                                                                    22228.946536389536, 0, -98211.52742441195,  0, 360108.93388951046, 0, -1114622.8906103896, 0,
                            2950472.35749809,  0, -6746401.706326042, 0, 13428551.967829932, 0, -23407080.70281818,  0,
                            35890857.07765454, 0, -48570248.182011135, 0, 58140740.434624165, 0, -61641688.24574132, 0,
                            57905828.35206003, 0, -48173756.36011717, 0, 35443154.078764886, 0, -23006959.66516317, 0,
                            13130801.369873613, 0, -6558130.030800664, 0, 2848480.7204487734, 0, -1067192.1293078198, 0,
                            341211.0889623641, 0, -91792.47334438503, 0, 20383.52455978361, 0, -3637.463978681924, 0,
                            501.4048090914933, 0, -50.11117612778805, 0, 3.2312124497699397, 0, -0.10092368634714097}
        }
};

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
        while (++cursor_bit_idx < cur_deg_total_bits) {
            if ((1 << cursor_bit_idx) & deg) {
                scheme.multAndEqual(tmp_ciphertext, tower[cursor_bit_idx]);
                scheme.reScaleByAndEqual(tmp_ciphertext, log_factor);
            } else {
                scheme.multByConstAndEqual(tmp_ciphertext, 1, log_factor);
                scheme.reScaleByAndEqual(tmp_ciphertext, log_factor);
            }
        }
        scheme.modDownToAndEqual(dst, tmp_ciphertext.logq);
        scheme.addAndEqual(dst, tmp_ciphertext);
    }
    return dst; // will RVO or NRVO optimize this out?
}


void plain_eval_poly(complex<double> *dst, const complex<double> *src, int len, const std::vector<double> &coeffs) {
    for (int i = 0; i < len; i++) {
        complex<double> src_i = src[i]; // handle the case when dst == src
        dst[i] = 0;
        for (int j = 0; j < coeffs.size(); j++) {
            dst[i] += coeffs[j] * pow(src_i, j);
        }
    }
}


Ciphertext homo_eval_mod(Scheme &scheme, Ciphertext &ciphertext, int n_iter, int K, double modulus, int deg) {
    auto &coeffs = coeff_map.at(deg);

    Ciphertext res = ciphertext;
    bool init = false;
    double range = K * modulus + modulus * 0.5;
    auto logp = ciphertext.logp;
    NTL_EXEC_RANGE(K, first, last)
                    for (int i = first + 1; i <= last; i++) {
                        // Step 1. adjust the inputs
                        // formula: sgn{(2k+1)/(4k-2(i-1))[x/range+(2k-1-2(i-1))/(2k+1)]}
                        //         =sgn{(2k+1)/[(4k-2(i-1))*range]x + (2k-1-2(i-1))/(4k-2(i-1))} denote as sgn{a*x +- b}
                        double a = (2 * K + 1) / (range * (4 * K - 2 * (i - 1)));
                        double b = double(2 * K - 1 - 2 * (i - 1)) / (4 * K - 2 * (i - 1));
                        for (int s = 0; s <= 1; s++) { // s == 0 mean ax+b, s == 1 means ax-b
                            Ciphertext tmp;
                            scheme.multByConst(tmp, ciphertext, a, logp);
                            scheme.reScaleByAndEqual(tmp, logp);
                            scheme.addConstAndEqual(tmp, s ? -b : b, logp);
                            // Step 2. composition of sign function
                            for (int j = 0; j <= n_iter; j++) { // NOTE: n_iter + 1 poly evals
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
    NTL_EXEC_RANGE_END
    // Step 4. Substract and multiply by q/2
    scheme.multByConstAndEqual(res, -modulus / 2, logp);
    scheme.reScaleByAndEqual(res, logp);
    Ciphertext cpy = ciphertext;
    scheme.modDownToAndEqual(cpy, res.logq);
    scheme.addAndEqual(res, cpy);
    return res;
}

void
plain_eval_mod(complex<double> *dst, const complex<double> *src, int len, int n_iter, int K, double modulus, int deg) {
    auto &coeffs = coeff_map.at(deg);
    std::vector<complex<double>> scratch(len);
    double range = K * modulus + modulus * 0.5;
    for (int i = 1; i <= K; i++) {
        // Step 1. adjust the inputs
        // formula: sgn{(2k+1)/(4k-2(i-1))[x/range+(2k-1-2(i-1))/(2k+1)]}
        //         =sgn{(2k+1)/[(4k-2(i-1))*range]x + (2k-1-2(i-1))/(4k-2(i-1))} denote as sgn{a*x +- b}
        double a = double(2 * K + 1) / (range * (4 * K - 2 * (i - 1)));
        double b = double(2 * K - 1 - 2 * (i - 1)) / (4 * K - 2 * (i - 1));
        for (int s = 0; s <= 1; s++) { // s == 0 mean ax+b, s == 1 means ax-b
            plain_eval_poly(scratch.data(), src, len, {s ? -b : b, a});
            // Step 2. composition of sign function
            for (int j = 0; j <= n_iter; j++) // NOTE: n_iter + 1 poly evals
                plain_eval_poly(scratch.data(), scratch.data(), len, coeffs);
            // Step 3. place the sign functions together
            for (int j = 0; j < len; j++)
                dst[j] += scratch[j];
        }
    }
    // Step 4. Substract and multiply by q/2
    for (int i = 0; i < len; i++)
        dst[i] = src[i] - dst[i] * modulus * 0.5;
}


// taylor approx in [-1/T, 1/T]
/**
 *
 * @param secretKey the secret key
 * @param scheme the ckks scheme
 * @param logq log2 of q=ciphertext modulus
 * @param logp log2 of p=scaling factor
 * @param logSlots log2 of number of slots
 * @param logT for bootstrapping
 * @param K number of intervals (half)
 * @param n_iter number of iterations to apply on the sign function
 * @param deg degree of the approximated sign function
 * @param samples_per_modulus number of samples in each modulus interval, used for deterministic sampling
 * @param modulus modulus of the approximated mod function
 * @param eps the distance of message from the nearest multiple of modulus is within eps*modulus
 * @param repeat number of times to repeat the homo eval
 * @param enable_boot test bootstrapping if true, else test mod function error
 * @param filename output filename
 */
void testBootstrap(SecretKey &secretKey, Scheme &scheme,
                   long logq, long logp, long logSlots, long logT,
                   int K, int n_iter, int deg, double modulus, double eps,
                   int repeat = 1, bool enable_boot = false, const std::string &filename = "") {
    long slots = (1 << logSlots);
    // test mod function
    if (!enable_boot) {
        // preprocessing
        std::vector<complex<double>> mod_input(slots);
        std::vector<complex<double>> expected(slots);
        double radius = modulus * eps;
        FILE *output = stdout;
        if (filename.length())
            output = fopen(filename.c_str(), "w");
        // header
        fprintf(output, "logq = %ld, logp = %ld, logSlots = %ld, logT = %ld, "
                        "K = %d, n_iter = %d, deg = %d, modulus = %f, eps = %f, repeat = %d, enable_boot = %d\n",
                logq, logp, logSlots, logT, K, n_iter, deg, modulus, eps, repeat, enable_boot);
        for (int n_ctxt = 0; n_ctxt < repeat; n_ctxt++) {
            // sample uniformly from Union_i={-K, -K+1,..., K}(i*modulus + (-radius, radius))
            for (int i = 0; i < slots; i++) {
                // sample double in (-radius, radius)
                auto rand_l = NTL::RandomBits_ulong(64);
                double bias = long(rand_l) / std::pow(2.0, 63) * radius;
                // sample nK in [-K, K]
                rand_l = (NTL::RandomBits_long(NumBits(2 * K + 1)) % (2 * K + 1));
                double real_val = (long(rand_l) - K) * modulus + bias;
                mod_input[i].real(real_val);
                double expected_rem = std::fmod(real_val, modulus);
                if (expected_rem > modulus / 2)
                    expected_rem -= modulus;
                expected[i].real(expected_rem);
            }
            fprintf(output, "%d th ciphertext\n", n_ctxt);
            Ciphertext dbg;
            scheme.encrypt(dbg, mod_input.data(), slots, logp, logq); // NOTE: use larger value here, logq is too small
            // messages in slots have bound of 1, so 3 * 0.4 is enough
            auto dbg_res = homo_eval_mod(scheme, dbg, n_iter, K, modulus, deg);
            auto dbg_vec = scheme.decrypt(secretKey, dbg_res);
            std::vector<complex<double>> plain_eval_vec(slots);
            plain_eval_mod(plain_eval_vec.data(), mod_input.data(), slots, n_iter, K, modulus, deg);
            for (int i = 0; i < slots; i++) {
                // sample idx, input, expected, plain_eval, homo_eval.real, homo_eval.imag
                fprintf(output, "%d, %f, %f, %f, %f, %f\n", i,
                        mod_input[i].real(), expected[i].real(),
                        plain_eval_vec[i].real(), dbg_vec[i].real(),
                        dbg_vec[i].imag());
            }
            fprintf(output, "\n");
            fflush(output);
        }
        if (output != stdout)
            fclose(output);
        return;
    }

    /*** bootstrapping test part ***/
    complex<double> *mvec = EvaluatorUtils::randomComplexArray(slots);
    Ciphertext cipher;
    scheme.encrypt(cipher, mvec, slots, logp, logq);
    cout << "cipher logq before: " << cipher.logq << endl;
    scheme.modDownToAndEqual(cipher, logq);
    scheme.normalizeAndEqual(cipher);
    cipher.logq = logQ;
    cipher.logp = logq + 4;
    Ciphertext rot;
    for (long i = logSlots; i < logNh; ++i) {
        scheme.leftRotateFast(rot, cipher, (1 << i));
        scheme.addAndEqual(cipher, rot);
    }
    scheme.divByPo2AndEqual(cipher, logNh);

    // FIXME: debug
    Plaintext before_c2s;
    scheme.decryptMsg(before_c2s, secretKey, cipher);

    scheme.coeffToSlotAndEqual(cipher);

    // FIXME: debug
    int print_num = 20;
    Plaintext before_mod;
    scheme.decryptMsg(before_mod, secretKey, cipher);
    before_mod.n = Nh; // number of total slots is N/2
    auto before_mod_slots = scheme.decode(before_mod);
    // confirm the effect of CoeffToSlot
/*     auto before_mod_q = ring.qpows[before_mod.logq];
     for(int i = 0; i < print_num; i++){
     auto expected = before_c2s.mx[i];
     rem(expected, expected, before_mod_q);
     if (NumBits(expected) == before_mod.logq) expected -= before_mod_q;
     auto got = before_mod_slots[i];
     std::cout << "i th coeff: " << expected << " ==> " << got << '\n';
     }*/

    scheme.evalExpAndEqual(cipher, logT);

    // FIXME: debug
    Plaintext after_mod;
    scheme.decryptMsg(after_mod, secretKey, cipher);
    after_mod.n = Nh;
    auto after_mod_slots = scheme.decode(after_mod);
    for (int i = 0; i < print_num; i++) {
        std::cout << "i th slot: " << before_mod_slots[i] << " ==> " << after_mod_slots[i]
                  << ", diff = " << after_mod_slots[i] - before_mod_slots[i] << '\n';
    }

    scheme.slotToCoeffAndEqual(cipher);
    cipher.logp = logp;
    cout << "cipher logq after: " << cipher.logq << endl;
    complex<double> *dvec = scheme.decrypt(secretKey, cipher);
    StringUtils::compare(mvec, dvec, slots, "boot");
}

struct TestParams {
    int n_iter, K, deg, repeat;
    double modulus, eps;
    bool enable_boot;
    std::string fname;
};

int main() {
    /*
  * Basic Parameters are in src/Params.h
  * If you want to use another parameter, you need to change src/Params.h file and re-complie this library.
  */

    // Parameters //
    long logq = 40; ///< Ciphertext modulus (this value should be <= logQ in "scr/Params.h")
    long logp = 30; ///< Scaling Factor (larger logp will give you more accurate value)
    long logn = 3; ///< number of slot is 1024 (this value should be < logN in "src/Params.h")

    long logT = 4;
    /**
     * 	long logq = 800; ///< Ciphertext Modulus
	 *  long logp = 30; ///< Real message will be quantized by multiplying 2^40
	 *  long logn = 4; ///< log2(The number of slots)
     */
    logq = 800;
    logp = 30;
    logn = 15;

    bool enable_boot = false;

    srand(time(nullptr));
    SetNumThreads(8);
    Ring ring;
    SecretKey secretKey(ring);
    Scheme scheme(secretKey, ring);

    if (enable_boot) {
        scheme.addBootKey(secretKey, logn, logq + 4);
    }

    std::vector<std::thread> threads;

    TestParams testParams[] = {
            {
                    2, 12, 31, 1, 1, pow(2.0, -7),  false, "2_12_31_-7"
            },
            {
                    2, 12, 31, 1, 1, pow(2.0, -10), false, "2_12_31_-10"
            },
            {
                    2, 12, 31, 1, 1, pow(2.0, -5),  false, "2_12_31_-5"
            },
            {
                    2, 12, 31, 1, 1, pow(2.0, -3),  false, "2_12_31_-3"
            }
    };

    for (auto &param: testParams) {
        threads.emplace_back(testBootstrap,
                             std::ref(secretKey), std::ref(scheme),
                             logq, logp, logn, logT,
                             param.K, param.n_iter, param.deg, param.modulus, param.eps,
                             param.repeat, param.enable_boot, param.fname);
    }
    for (auto &e: threads)
        e.join();
}
