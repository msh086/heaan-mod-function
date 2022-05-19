#include <iostream>
#include <cmath>
#include <thread>
#include <map>
#include <mutex>
#include <HEAAN.h>

using namespace NTL;
using namespace heaan;
using std::cout, std::endl, std::complex;

static std::map<int, std::vector<RR>> coeff_map;

/**
 *
 * @param scheme
 * @param ciphertext
 * @param coeffs from the lowest term to the highest term
 * @return
 */
template<typename T>
Ciphertext homo_eval_poly(Scheme &scheme, const Ciphertext &ciphertext, std::vector<T> &coeffs) {
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


void plain_eval_poly(complex<double> *dst, const complex<double> *src, int len, const std::vector<RR> &coeffs) {
    for (int i = 0; i < len; i++) {
        complex<double> src_i = src[i]; // handle the case when dst == src
        dst[i] = 0;
        for (int j = 0; j < coeffs.size(); j++) {
            dst[i] += conv<double, RR>(coeffs[j]) * pow(src_i, j);
        }
    }
}


Ciphertext homo_eval_mod(Scheme &scheme, Ciphertext &ciphertext, int n_iter, int K, const RR& modulus, int deg) {
    auto &coeffs = coeff_map.at(deg);

    Ciphertext res = ciphertext;
    bool init = false;
    RR range = (K + 0.5) * modulus;
    auto logp = ciphertext.logp;
    std::mutex mutex; // writer lock for init and res
    int dK = 2 * K;
    std::vector<std::thread> threads;
    auto f = [&](int i) {
        int s = 0;
        if (i > K) {
            i -= K;
            s = 1; // s == 0 mean ax+b, s == 1 means ax-b
        }
        // Step 1. adjust the inputs
        // formula: sgn{(2k+1)/(4k-2(i-1))[x/range+(2k-1-2(i-1))/(2k+1)]}
        //         =sgn{(2k+1)/[(4k-2(i-1))*range]x + (2k-1-2(i-1))/(4k-2(i-1))} denote as sgn{a*x +- b}
        RR a = RR(2 * K + 1) / (range * (4 * K - 2 * (i - 1)));
        RR b = RR(2 * K - 1 - 2 * (i - 1)) / RR(4 * K - 2 * (i - 1));

        Ciphertext tmp;
        scheme.multByConst(tmp, ciphertext, a, logp);
        scheme.reScaleByAndEqual(tmp, logp);
        RR signed_b = s ? -b : b;
        scheme.addConstAndEqual(tmp, signed_b, logp);
        // Step 2. composition of sign function
        for (int j = 0; j <= n_iter; j++) { // NOTE: n_iter + 1 poly evals
            // NOTE: no operator= for Ciphertext, so `tmp = homo_eval_poly(...)` will cause SIGSEGV
            auto iterated = homo_eval_poly(scheme, tmp, coeffs);
            tmp.copy(iterated);
        }
        // Step 3. place the sign functions together
        // NOTE: use mutex to ensure thread safety
        mutex.lock();
        if (!init) {
            res.copy(tmp); // NOTE: use copy here too!
            init = true;
        } else
            scheme.addAndEqual(res, tmp);
        mutex.unlock();
    };
    for (int i = 1; i <= dK; i++)
        threads.emplace_back(f, i);
    for (auto &t: threads)
        t.join();
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


void evalExpAndEqualNew(Scheme &scheme, Ring &ring, Ciphertext &cipher, long logT, long logI, int n_iter, int K, int deg) {
    long slots = cipher.n;
    long logSlots = log2(slots);
    BootContext *bootContext = ring.bootContextMap.at(logSlots);
    if (logSlots < logNh) {
        Ciphertext tmp;
        scheme.conjugate(tmp, cipher);
        scheme.subAndEqual(cipher, tmp);
        scheme.idivAndEqual(cipher);
        scheme.divByPo2AndEqual(cipher, 1);
        // scheme.divByPo2AndEqual(cipher, logT + 1); // bitDown: logT + 1
        auto ret_val = homo_eval_mod(scheme, cipher, n_iter, K, RR(pow(2, -4)), deg);
        cipher.copy(ret_val);
        RR c = 16 * 2 * 2 *
               Pi; // 2Pi because of the coeff of sign function, 2 because the extracted imag part wasn't divided by 2
        scheme.multByConstAndEqual(cipher, c, bootContext->logp); // note that bootContext->logp == cipher.logp
        scheme.reScaleByAndEqual(cipher, bootContext->logp);
        scheme.imultAndEqual(cipher);
        // exp2piAndEqual(cipher, bootContext->logp); // bitDown: logT + 1 + 3(logq + logI)
        // for (long i = 0; i < logI + logT; ++i) {
        // squareAndEqual(cipher);
        // reScaleByAndEqual(cipher, bootContext->logp);
        // }
        // scheme.conjugate(tmp, cipher);
        // scheme.subAndEqual(cipher, tmp);

        scheme.multByPolyNTT(tmp, cipher, bootContext->rp1, bootContext->bnd1, bootContext->logp);
        Ciphertext tmprot;
        scheme.leftRotateFast(tmprot, tmp, slots);
        scheme.addAndEqual(tmp, tmprot);
        scheme.multByPolyNTTAndEqual(cipher, bootContext->rp2, bootContext->bnd2, bootContext->logp);
        scheme.leftRotateFast(tmprot, cipher, slots);
        scheme.addAndEqual(cipher, tmprot);
        scheme.addAndEqual(cipher, tmp);
    } else {} // TODO
    scheme.reScaleByAndEqual(cipher, bootContext->logp + logI);
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
void testBootstrap(SecretKey &secretKey, Scheme &scheme, Ring &ring,
                   long logq, long logp, long logSlots, long logT,
                   int K, int n_iter, int deg, const RR& modulus, const RR& eps,
                   int repeat = 1, bool enable_boot = false, const std::string &filename = "") {
    long slots = (1 << logSlots);
    // test mod function
    if (!enable_boot) { // FIXME update to RR?? is it necessary?
        // preprocessing
        std::vector<complex<double>> mod_input(slots);
        std::vector<complex<double>> expected(slots);
        double radius = to_double(modulus) * to_double(eps);

        FILE *output = stdout;
        if (filename.length())
            output = fopen(filename.c_str(), "w");

        // header
        fprintf(output, "logq = %ld, logp = %ld, logSlots = %ld, logT = %ld, "
                        "K = %d, n_iter = %d, deg = %d, modulus = %f, eps = %f, repeat = %d, enable_boot = %d\n",
                logq, logp, logSlots, logT, K, n_iter, deg, to_double(modulus), to_double(eps), repeat, enable_boot);

        for (int n_ctxt = 0; n_ctxt < repeat; n_ctxt++) {
            // sample uniformly from Union_i={-K, -K+1,..., K}(i*modulus + (-radius, radius))
            for (int i = 0; i < slots; i++) {
                // sample double in (-radius, radius)
                auto rand_l = NTL::RandomBits_ulong(64);
                double bias = long(rand_l) / std::pow(2.0, 63) * radius;
                // sample nK in [-K, K]
                rand_l = (NTL::RandomBits_long(NumBits(2 * K + 1)) % (2 * K + 1));
                double real_val = (long(rand_l) - K) * to_double(modulus) + bias;
                mod_input[i].real(real_val);
                double expected_rem = std::fmod(real_val, to_double(modulus));
                if (expected_rem > modulus / 2)
                    expected_rem -= to_double(modulus);
                expected[i].real(expected_rem);
            }

            fprintf(output, "%d th ciphertext\n", n_ctxt);
            Ciphertext dbg;
            scheme.encrypt(dbg, mod_input.data(), slots, logp, logq); // NOTE: use larger value here, logq is too small
            // messages in slots have bound of 1, so 3 * 0.4 is enough
            auto dbg_res = homo_eval_mod(scheme, dbg, n_iter, K, modulus, deg);
            auto dbg_vec = scheme.decrypt(secretKey, dbg_res);
            std::vector<complex<double>> plain_eval_vec(slots);
            plain_eval_mod(plain_eval_vec.data(), mod_input.data(), slots, n_iter, K, to_double(modulus), deg);

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
    FILE *output = stdout;
    if (filename.length())
        output = fopen(filename.c_str(), "w");

//    complex<double> *mvec = EvaluatorUtils::randomComplexArray(slots);

    // sample from [-eps*q, eps*q]
    Plaintext bounded_ptxt(logp, logq, slots);
    // freshly encoded ptxt will have scaling factor of logp + logQ, where the logQ bits are removed during encryption
    NTL::ZZ range = to_ZZ(to_RR(ZZ(1) << logq) * eps);
    for (int i = 0; i < N; i += Nh / slots) { // follow the encoding rule in heaan
       bounded_ptxt.mx[i] = (NTL::RandomBnd(range * 2) - range) << logQ;
    }
    Ciphertext cipher;
    scheme.encryptMsg(cipher, bounded_ptxt);
    Plaintext actual_ptxt(logp, logq, slots);
    for (int i = 0; i < N; i += Nh / slots)
        actual_ptxt.mx[i] = bounded_ptxt.mx[i] >> logQ;
    auto mvec = scheme.decode(actual_ptxt);


    printf("before boot: logp = %ld, logq = %ld\n", cipher.logp, cipher.logq);

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

    printf("before c2s: logp = %ld, logq = %ld\n", cipher.logp, cipher.logq);

    // FIXME: debug
    Plaintext before_c2s;
    scheme.decryptMsg(before_c2s, secretKey, cipher);

    scheme.coeffToSlotAndEqual(cipher);

    // FIXME: debug
    Plaintext before_mod;
    scheme.decryptMsg(before_mod, secretKey, cipher);
    before_mod.n = Nh; // number of total slots is N/2
    auto before_mod_slots = scheme.decode(before_mod);

    printf("before mod: logp = %ld, logq = %ld\n", cipher.logp, cipher.logq);

#define DBG_MOD
#ifdef DBG_MOD
    Ciphertext mod_boot_out_real(cipher);
    evalExpAndEqualNew(scheme, ring, mod_boot_out_real, logT, 4, n_iter, K, deg);
    printf("after mod new: logp = %ld, logq = %ld\n", mod_boot_out_real.logp, mod_boot_out_real.logq);
#endif
    scheme.evalExpAndEqual(cipher, logT); // TODO update to RR too

    // FIXME: debug
    printf("after mod: logp = %ld, logq = %ld\n", cipher.logp, cipher.logq);
    Plaintext after_mod;
    scheme.decryptMsg(after_mod, secretKey, cipher);
    after_mod.n = Nh;
    auto after_mod_slots = scheme.decode(after_mod);

#ifdef DBG_MOD
    // print the values of ALL the slots to file(before and after mod)
    Plaintext mod_boot_out_msg_new;
    scheme.decryptMsg(mod_boot_out_msg_new, secretKey, mod_boot_out_real);
    mod_boot_out_msg_new.n = Nh; // NOTE: important, different n has different embeddings
    auto mod_boot_out_slots_new = scheme.decode(mod_boot_out_msg_new);
    for (int i = 0; i < Nh; i++) {
        double before_real = before_mod_slots[i].real(), before_imag = before_mod_slots[i].imag(),
                after_real = after_mod_slots[i].real(), after_imag = after_mod_slots[i].imag();
        auto after_new = mod_boot_out_slots_new[i];
        double after_real_new = after_new.real(), after_imag_new = after_new.imag();
        fprintf(output, "%d, (%f, %f), (%f, %f), (%f, %f) ## (%f, %f), (%f, %f)\n", i,
                before_real, before_imag, after_real, after_imag, after_real - before_real, after_imag - before_imag,
                after_real_new, after_imag_new, after_real_new - before_real, after_imag_new - before_imag);
    }
#endif

    scheme.slotToCoeffAndEqual(cipher);
    printf("after s2c: logp = %ld, logq = %ld\n", cipher.logp, cipher.logq);
#ifdef DBG_MOD
    scheme.slotToCoeffAndEqual(mod_boot_out_real);
    printf("after s2c new: logp = %ld, logq = %ld\n", mod_boot_out_real.logp, mod_boot_out_real.logq);
    mod_boot_out_real.logp = logp;
#endif
    cipher.logp = logp;
    printf("after boot: logp = %ld, logq = %ld\n", cipher.logp, cipher.logq);


    Plaintext dmsg, dmsg_new;
    scheme.decryptMsg(dmsg, secretKey, cipher);
#ifdef DBG_MOD
    scheme.decryptMsg(dmsg_new, secretKey, mod_boot_out_real);
#endif

    auto q0 = ring.qpows[logq], q1 = ring.qpows[dmsg.logq], q2 = ring.qpows[dmsg_new.logq];
    for (int i = 0; i < N; i++) {
        auto expected = actual_ptxt.mx[i];
        NTL::rem(expected, expected, q0);
        if (NTL::NumBits(expected) >= logq)
            expected -= q0;
        auto got = dmsg.mx[i];
        NTL::rem(got, got, q1);
        if (NTL::NumBits(got) >= dmsg.logq)
            got -= q1;
        fprintf(output, "%ld, %ld, %ld", to_long(expected), to_long(got), to_long(got - expected));
#ifdef DBG_MOD
        auto got_new = dmsg_new.mx[i];
        NTL::rem(dmsg_new.mx[i], dmsg_new.mx[i], q2);
        if (NTL::NumBits(got_new) >= dmsg_new.logq)
            got_new -= q2;
        fprintf(output, ", %ld, %ld", to_long(got_new), to_long(got_new - expected));
#endif
        fprintf(output, "\n");
    }


    auto *dvec = scheme.decode(dmsg);
    StringUtils::compare(mvec, dvec, slots, "boot");
#ifdef DBG_MOD
    auto dvec_new = scheme.decode(dmsg_new);
    StringUtils::compare(mvec, dvec_new, slots, "boot new");
#endif

    if (output != stdout)
        fclose(output);
}

struct TestParams {
    int n_iter, K, deg, repeat;
    RR modulus, eps;
    bool enable_boot;
    std::string fname;
};

using uchar = unsigned char;

int main() {
    RR::SetPrecision(100);
    coeff_map = {
            {15, {RR(0), to_RR(ZZFromBytes((uchar*)"\x23\x19", 2)) / to_RR(ZZFromBytes((uchar*)"\x00\x08", 2)), RR(0), -to_RR(ZZFromBytes((uchar*)"\xa7\x3a", 2)) / to_RR(ZZFromBytes((uchar*)"\x00\x08", 2)), RR(0), to_RR(ZZFromBytes((uchar*)"\x93\x69", 2)) / to_RR(ZZFromBytes((uchar*)"\x00\x08", 2)), RR(0), -to_RR(ZZFromBytes((uchar*)"\xaf\x7d", 2)) / to_RR(ZZFromBytes((uchar*)"\x00\x08", 2)), RR(0), to_RR(ZZFromBytes((uchar*)"\xc1\x61", 2)) / to_RR(ZZFromBytes((uchar*)"\x00\x08", 2)), RR(0), -to_RR(ZZFromBytes((uchar*)"\xfd\x2f", 2)) / to_RR(ZZFromBytes((uchar*)"\x00\x08", 2)), RR(0), to_RR(ZZFromBytes((uchar*)"\x89\x0d", 2)) / to_RR(ZZFromBytes((uchar*)"\x00\x08", 2)), RR(0), -to_RR(ZZFromBytes((uchar*)"\xad\x01", 2)) / to_RR(ZZFromBytes((uchar*)"\x00\x08", 2))}},
            {31, {RR(0), to_RR(ZZFromBytes((uchar*)"\x23\xe1\xe9\x11", 4)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x04", 4)), RR(0), -to_RR(ZZFromBytes((uchar*)"\xaf\x65\x91\x59", 4)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x04", 4)), RR(0), to_RR(ZZFromBytes((uchar*)"\xdf\x77\x2f\x78\x01", 5)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x04", 4)), RR(0), -to_RR(ZZFromBytes((uchar*)"\xe3\x29\x62\x8c\x04", 5)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x04", 4)), RR(0), to_RR(ZZFromBytes((uchar*)"\x67\x0c\xe5\x9c\x0a", 5)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x04", 4)), RR(0), -to_RR(ZZFromBytes((uchar*)"\x53\x16\x69\x1a\x13", 5)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x04", 4)), RR(0), to_RR(ZZFromBytes((uchar*)"\xa3\x95\xbb\xf0\x1a", 5)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x04", 4)), RR(0), -to_RR(ZZFromBytes((uchar*)"\xa7\x47\xee\x04\x1e", 5)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x04", 4)), RR(0), to_RR(ZZFromBytes((uchar*)"\x39\x3f\xd2\x7c\x1a", 5)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x04", 4)), RR(0), -to_RR(ZZFromBytes((uchar*)"\x7d\x30\xd1\x6e\x12", 5)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x04", 4)), RR(0), to_RR(ZZFromBytes((uchar*)"\x8d\xc2\xa4\x01\x0a", 5)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x04", 4)), RR(0), -to_RR(ZZFromBytes((uchar*)"\xb9\xf9\x21\x27\x04", 5)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x04", 4)), RR(0), to_RR(ZZFromBytes((uchar*)"\x7d\x01\x07\x46\x01", 5)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x04", 4)), RR(0), -to_RR(ZZFromBytes((uchar*)"\xc1\xf9\xa9\x45", 4)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x04", 4)), RR(0), to_RR(ZZFromBytes((uchar*)"\xb1\x01\x44\x09", 4)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x04", 4)), RR(0), -to_RR(ZZFromBytes((uchar*)"\x7d\xee\x93", 3)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x04", 4))}},
            {63, {RR(0), to_RR(ZZFromBytes((uchar*)"\x23\x21\xd8\x27\xf9\x64\xb7\x0c", 8)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x00\x00\x00\x00\x02", 8)), RR(0), -to_RR(ZZFromBytes((uchar*)"\xbf\xab\x0e\xf1\x63\x13\x67\x83", 8)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x00\x00\x00\x00\x02", 8)), RR(0), to_RR(ZZFromBytes((uchar*)"\xb7\x09\x84\x79\x83\xae\x9f\x9e\x04", 9)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x00\x00\x00\x00\x02", 8)), RR(0), -to_RR(ZZFromBytes((uchar*)"\xcb\xb0\x8f\xa8\x42\x47\xbc\xe5\x1f", 9)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x00\x00\x00\x00\x02", 8)), RR(0), to_RR(ZZFromBytes((uchar*)"\xc3\x50\x0e\xeb\x6a\xa0\xe4\xa9\xad", 9)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x00\x00\x00\x00\x02", 8)), RR(0), -to_RR(ZZFromBytes((uchar*)"\x2f\xd9\xd8\x90\x92\x0a\x0e\x47\xff\x02", 10)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x00\x00\x00\x00\x02", 8)), RR(0), to_RR(ZZFromBytes((uchar*)"\x57\x1c\x1b\x13\xc4\x26\xde\x59\xfd\x0a", 10)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x00\x00\x00\x00\x02", 8)), RR(0), -to_RR(ZZFromBytes((uchar*)"\x7b\x88\x3b\xc1\x15\xfe\xc7\xfd\x03\x22", 10)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x00\x00\x00\x00\x02", 8)), RR(0), to_RR(ZZFromBytes((uchar*)"\xaf\xd2\xd9\x59\xfd\x09\xb7\x90\x0a\x5a", 10)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x00\x00\x00\x00\x02", 8)), RR(0), -to_RR(ZZFromBytes((uchar*)"\xdb\xa5\xc6\x25\x91\xa3\x69\x43\xe2\xcd", 10)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x00\x00\x00\x00\x02", 8)), RR(0), to_RR(ZZFromBytes((uchar*)"\x13\x60\x16\x9e\x67\x87\xef\x8f\xce\x99\x01", 11)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x00\x00\x00\x00\x02", 8)), RR(0), -to_RR(ZZFromBytes((uchar*)"\x17\x32\xe2\xd9\xc8\xd7\x67\xd1\x53\xca\x02", 11)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x00\x00\x00\x00\x02", 8)), RR(0), to_RR(ZZFromBytes((uchar*)"\xdf\x5d\xe3\x1a\x56\xc2\x27\x52\x4d\x47\x04", 11)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x00\x00\x00\x00\x02", 8)), RR(0), -to_RR(ZZFromBytes((uchar*)"\x5b\x50\x2f\x3d\x90\x30\x5d\x10\x3f\xca\x05", 11)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x00\x00\x00\x00\x02", 8)), RR(0), to_RR(ZZFromBytes((uchar*)"\x03\x4c\x67\x06\x0f\x87\xde\x88\x50\xee\x06", 11)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x00\x00\x00\x00\x02", 8)), RR(0), -to_RR(ZZFromBytes((uchar*)"\x17\xb8\x6f\x6a\xce\xd1\x7d\xb0\x27\x59\x07", 11)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x00\x00\x00\x00\x02", 8)), RR(0), to_RR(ZZFromBytes((uchar*)"\xa9\x95\xf4\x44\x36\x41\xb4\x48\x25\xe7\x06", 11)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x00\x00\x00\x00\x02", 8)), RR(0), -to_RR(ZZFromBytes((uchar*)"\x3d\x5c\xad\xf6\x46\x61\xb8\x78\x25\xbe\x05", 11)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x00\x00\x00\x00\x02", 8)), RR(0), to_RR(ZZFromBytes((uchar*)"\x65\x4f\x8a\xe0\xde\x53\x28\xa4\xa3\x39\x04", 11)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x00\x00\x00\x00\x02", 8)), RR(0), -to_RR(ZZFromBytes((uchar*)"\x61\x84\xe0\x52\x44\x90\x54\xdf\x1d\xbe\x02", 11)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x00\x00\x00\x00\x02", 8)), RR(0), to_RR(ZZFromBytes((uchar*)"\xa9\xdd\x97\x03\x13\x60\xbd\x62\xb8\x90\x01", 11)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x00\x00\x00\x00\x02", 8)), RR(0), -to_RR(ZZFromBytes((uchar*)"\x2d\x8e\x3a\xca\x1a\xc5\x0f\x64\x23\xc8", 10)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x00\x00\x00\x00\x02", 8)), RR(0), to_RR(ZZFromBytes((uchar*)"\xe5\x23\x98\x5f\xa9\xde\x70\xc1\xed\x56", 10)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x00\x00\x00\x00\x02", 8)), RR(0), -to_RR(ZZFromBytes((uchar*)"\x91\x8d\x33\x72\xa2\x34\x42\x70\x91\x20", 10)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x00\x00\x00\x00\x02", 8)), RR(0), to_RR(ZZFromBytes((uchar*)"\x45\x92\x31\x99\x79\x8c\x2d\xb6\x69\x0a", 10)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x00\x00\x00\x00\x02", 8)), RR(0), -to_RR(ZZFromBytes((uchar*)"\xe9\xb6\xd4\xfa\x31\x5a\xf2\x20\xcd\x02", 10)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x00\x00\x00\x00\x02", 8)), RR(0), to_RR(ZZFromBytes((uchar*)"\x91\x3b\xd1\x96\x19\x93\x0c\x3f\x9f", 9)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x00\x00\x00\x00\x02", 8)), RR(0), -to_RR(ZZFromBytes((uchar*)"\x7d\x24\xcf\x21\x9d\x8e\xed\x6a\x1c", 9)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x00\x00\x00\x00\x02", 8)), RR(0), to_RR(ZZFromBytes((uchar*)"\xf5\x97\x2c\x22\x23\x43\xcf\xea\x03", 9)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x00\x00\x00\x00\x02", 8)), RR(0), -to_RR(ZZFromBytes((uchar*)"\x89\x23\xe4\xd1\x13\xec\x38\x64", 8)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x00\x00\x00\x00\x02", 8)), RR(0), to_RR(ZZFromBytes((uchar*)"\x01\x3f\x61\x6c\x7a\x61\x76\x06", 8)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x00\x00\x00\x00\x02", 8)), RR(0), -to_RR(ZZFromBytes((uchar*)"\x1d\x66\x81\xf8\x44\xac\x33", 7)) / to_RR(ZZFromBytes((uchar*)"\x00\x00\x00\x00\x00\x00\x00\x02", 8))}}
    };
    std::map<int, std::vector<double>> baseline_map =
    {
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
    for(auto &k : coeff_map){
        auto &RR_vec = k.second;
        auto &double_vec = baseline_map.at(k.first);
        if(RR_vec.size() != double_vec.size()){
            fprintf(stderr, "size mismatch\n");
            return 1;
        }
        int len = RR_vec.size();
        for(int i = 0; i < len; i++){
            if(fabs(to_double(RR_vec[i]) - double_vec[i]) > 0.1){
                fprintf(stderr, "coeffs mismatch: RR=%f double=%f\n", to_double(RR_vec[i]), double_vec[i]);
                return 1;
            }
        }
    }
    printf("coeffs check pass\n");
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
//    logq = 800;
    logp = 30;
    logn = 3;

    bool enable_boot = true;

    srand(time(nullptr));
    SetNumThreads(16);
    Ring ring;
    SecretKey secretKey(ring);
    Scheme scheme(secretKey, ring);

    if (enable_boot) {
        scheme.addBootKey(secretKey, logn, logq + 4);
    }
//    testBootstrap(secretKey, scheme, ring,
//                  logq, logp, logn, logT,
//                  8, 3, 31, pow(2.0, -4), pow(2.0, -10),
//                  0, true, "test_boot");
//    return 0;

    // FIXME: debug
    /* int slots = 1 << logn;
    int K = 16;
    double radius = pow(2, -4);
    Ciphertext ctxt;
    std::vector<complex<double>> test_vec(slots);
    for (int i = 0; i < slots; i++) {
        // sample double in (-radius, radius)
        auto rand_l = NTL::RandomBits_ulong(64);
        double bias = long(rand_l) / std::pow(2.0, 63) * radius;
        // sample nK in [-K, K]
        double real_val = bias;
        test_vec[i].real(real_val);
    }
    scheme.encrypt(ctxt, test_vec.data(), slots, logp, logq);
    scheme.squareAndEqual(ctxt);
    scheme.reScaleByAndEqual(ctxt, logp);
    auto dec_vec = scheme.decrypt(secretKey, ctxt);
    //FILE* f = fopen("error test", "w");
    // for(int i = 0; i < slots; i++){
        // fprintf(f, "%f -> (%f, %f), diff in real = %f\n",
            // test_vec[i].real(), dec_vec[i].real(), dec_vec[i].imag(), dec_vec[i].real() - test_vec[i].real() * test_vec[i].real());
    // }
    double mean = 0;
    for(int i = 0; i < slots; i++)
        mean += std::abs(dec_vec[i].real() - test_vec[i].real() * test_vec[i].real());
    mean /= slots;
    cout << "mean = " << mean << '\n';
    //fclose(f); */
    //return 0; // FIXME: finish debug


    std::vector<std::thread> threads;

    TestParams testParams[] = {
            {
                    3, 8, 31, 1, RR(pow(2.0, -4)), RR(pow(2.0, -7)), true, "2_12_31_-4_-7_RR"
            },
//           {
//                   3, 8, 31, 1, RR(pow(2.0, -4)), RR(pow(2.0, -10)), true, "2_12_31_-4_-10"
//           },
//           {
//                   3, 8, 31, 1, RR(pow(2.0, -4)), RR(pow(2.0, -5)),  true, "2_12_31_-4_-5"
//           },
//           {
//                   3, 8, 31, 1, RR(pow(2.0, -4)), RR(pow(2.0, -3)),  true, "2_12_31_-4_-3"
//           }
    };

    for (auto &param: testParams) {
        threads.emplace_back(testBootstrap,
                             std::ref(secretKey), std::ref(scheme), std::ref(ring),
                             logq, logp, logn, logT,
                             param.K, param.n_iter, param.deg, param.modulus, param.eps,
                             param.repeat, param.enable_boot, param.fname);
    }
    for (auto &e: threads)
        e.join();
}
