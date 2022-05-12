#include <iostream>
#include <cmath>
#include <thread>
#include <HEAAN.h>

using namespace NTL;
using namespace heaan;
using std::cout, std::endl, std::complex;

// TODO: mapping from deg to coeffs

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
        } // FIXME: use moddownto instead
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
        complex<double> src_i = src[i]; // handle the case when dst == src
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

    Ciphertext res = ciphertext;
    bool init = false;
    double range = K * modulus + modulus * 0.5;
    auto logp = ciphertext.logp;
    for (int i = 1; i <= K; i++) {
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
    // Step 4. Substract and multiply by q/2
    scheme.multByConstAndEqual(res, -modulus / 2, logp);
    scheme.reScaleByAndEqual(res, logp);
	Ciphertext cpy = ciphertext;
	scheme.modDownToAndEqual(cpy, res.logq);
	scheme.addAndEqual(res, cpy);
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
        //         =sgn{(2k+1)/[(4k-2(i-1))*range]x + (2k-1-2(i-1))/(4k-2(i-1))} denote as sgn{a*x +- b}
        double a = double(2 * K + 1) / (range * (4 * K - 2 * (i - 1)));
        double b = double(2 * K - 1 - 2 * (i - 1)) / (4 * K - 2 * (i - 1));
        for (int s = 0; s <= 1; s++) { // s == 0 mean ax+b, s == 1 means ax-b
            plain_eval_poly(scratch.data(), src, len, {s ? -b : b, a});
            // Step 2. composition of sign function
            for (int j = 0; j <= n_iter; j++) // NOTE: n_iter + 1 poly evals
                plain_eval_poly(scratch.data(), scratch.data(), len, coeffs);
            // Step 3. place the sign functions together
            for(int j = 0; j < len; j++)
                dst[j] += scratch[j];
        }
    }
    // Step 4. Substract and multiply by q/2
    for(int i = 0; i < len; i++)
        dst[i] = src[i] - dst[i] * modulus * 0.5;
}


// taylor approx in [-1/T, 1/T]
/*
	parameters:
		Ring parameters: logn, logq, logp
		Mod parameters: K, n_iter, modulus
*/
void testBootstrap(SecretKey& secretKey, Scheme& scheme, 
		long logq, long logp, long logSlots, long logT, 
		int K, int n_iter, int deg, double modulus, 
		int repeat=1, bool enable_boot=false, const std::string& filename="") {
    
	long slots = (1 << logSlots);
	
	if(!enable_boot) {
		// test mod function
		double range = K * modulus + modulus * 0.5;
		int samples_per_modulus = 100;
		int samples_per_pack = samples_per_modulus * (2 * K + 1) + 1;
		int packs_per_ctxt = slots / samples_per_pack;
		int used_slots = packs_per_ctxt * samples_per_pack;
		
		std::vector<complex<double>> mod_input(slots);
		std::vector<complex<double>> expected(samples_per_pack);
		// sample uniformly from Union_i={-K, -K+1,..., K}(i*modulus + (-radius, radius))
		// double ratio = pow(2.0, -2), radius = modulus * ratio;
	/*     for(auto & e : mod_input){
			// sample double in (-radius, radius)
			auto rand_l = NTL::RandomBits_ulong(64);
			double bias = long(rand_l) / std::pow(2.0, 63) * radius;
			// sample nK in [-K, K]
			rand_l = (NTL::RandomBits_long(NumBits(2 * K + 1)) % (2 * K + 1));
			e.real((long(rand_l) - K) * modulus + bias);
		} */
		for(int i = 0; i < samples_per_pack; i++) {
			double tmp = -range + i * modulus / samples_per_modulus;
			double expected_rem = std::fmod(tmp, modulus);
			if(expected_rem > modulus / 2)
				expected_rem -= modulus;
			expected[i].real(expected_rem);
			for(int j = 0; j < packs_per_ctxt; j++)
				mod_input[i + j * samples_per_pack].real(tmp);
		}
		
		
		FILE* output = stdout;
		if(filename.length())
			output = fopen(filename.c_str(), "w");
		
		Ciphertext dbg;
		scheme.encrypt(dbg, mod_input.data(), slots, logp, logq); // NOTE: use larger value here, logq is too small


		// messages in slots have bound of 1, so 3 * 0.4 is enough
		auto dbg_res = homo_eval_mod(scheme, dbg, n_iter, K, modulus);
		auto dbg_vec = scheme.decrypt(secretKey, dbg_res);

		std::vector<double> mod_coeffs{0, 4.47839789092541, 0, -22.391989454627, 0, 94.0463557094336, 0, -291.095862910151, 0,
									   679.223680123687, 0, -1222.60262422264, 0, 1724.18318800628, 0, -1921.232695207, 0,
									   1695.20531930029, 0, -1179.70428653061, 0, 640.410898402333, 0, -265.783179178834, 0,
									   81.5068416148424, 0, -17.4159917980433, 0, 2.3164127022028, 0, -0.144464448094368};
		std::vector<complex<double>> plain_eval_vec(used_slots);
		plain_eval_mod(plain_eval_vec.data(), mod_input.data(), used_slots, n_iter, K, modulus);

		for(int i = 0; i < packs_per_ctxt; i++){
			fprintf(output, "pack %d\n", i);
			int start_idx = i * samples_per_pack;
			for(int j = 0; j < samples_per_pack; j++){
				// sample idx, expected, plain_eval, homo_eval
				fprintf(output, "%d, %f, %f, %f, %f\n", j, expected[start_idx + j], mod_input[start_idx + j], 
					plain_eval_vec[start_idx + j], dbg_vec[start_idx + j]);
			}
		}

		if(filename.length())
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
	// auto before_mod_q = ring.qpows[before_mod.logq];
	// for(int i = 0; i < print_num; i++){
	   // auto expected = before_c2s.mx[i];
	   // rem(expected, expected, before_mod_q);
	   // if (NumBits(expected) == before_mod.logq) expected -= before_mod_q;

	   // auto got = before_mod_slots[i];
	   // std::cout << "i th coeff: " << expected << " ==> " << got << '\n';
	// }


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
	logq = 800;
	logp = 30;
	logn = 15;
	
	bool enable_boot = false;

	
    srand(time(nullptr));
    SetNumThreads(8);
    Ring ring;
    SecretKey secretKey(ring);
    Scheme scheme(secretKey, ring);

	if(enable_boot){
		scheme.addBootKey(secretKey, logn, logq + 4);
	}
	
	
    int n_iter = 3, K = 16, deg = 31;
    double modulus = 1;
	
	int repeat = 1;
	std::string filename = "output";
	int n_threads = 1; // FIXME
	
	std::vector<std::thread> threads;
	
	for(int i = 0; i < n_threads; i++){
		threads.emplace_back(testBootstrap,
			std::ref(secretKey), std::ref(scheme), 
			logq, logp, logn, logT,
			K, n_iter, 31, modulus,
			repeat, enable_boot, filename + std::to_string(i)); // FIXME
	}
	for(auto &e : threads)
		e.join();
}
