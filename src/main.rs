use std::time::{Instant};

use ark_ff::{Field, /* FftField */ };
use ark_poly::{
    Polynomial,
    univariate::DensePolynomial, 
    EvaluationDomain, 
    Radix2EvaluationDomain,
    Evaluations
};
use ark_std::rand::Rng;
use ark_std::{UniformRand, test_rng, ops::*};
use ark_bls12_381::{Bls12_381};
use ark_ec::{pairing::Pairing, CurveGroup};
use ark_ec::{VariableBaseMSM};

use kzg::*;

mod utils;
mod kzg;

type KZG = KZG10::<Bls12_381, UniPoly381>;
type UniPoly381 = DensePolynomial<<Bls12_381 as Pairing>::ScalarField>;
type F = ark_bls12_381::Fr;
type G1 = <Bls12_381 as Pairing>::G1Affine;
type G2 = <Bls12_381 as Pairing>::G2Affine;

struct Proof {
    agg_pk: G1,
    agg_weight: F,

    r: F,

    merged_proof: G1,

    psw_of_r: F,

    psw_of_r_div_ω: F,
    psw_of_r_div_ω_proof: G1,
    w_of_r: F,
    b_of_r: F,
    psw_wff_q_of_r: F,
    psw_check_q_of_r: F,
    b_wff_q_of_r: F,
    b_check_q_of_r: F,

    psw_of_x_com: G1,
    b_of_x_com: G1,
    psw_wff_q_of_x_com: G1,
    psw_check_q_of_x_com: G1,
    b_wff_q_of_x_com: G1,
    b_check_q_of_x_com: G1,

    sk_q1_com: G1,
    sk_q2_com: G1,
}

struct ProverPreprocessing {
    n: usize, //size of the committee as a power of 2
    pks: Vec<G1>, //g^sk_i for each party i
    q1_coms : Vec<G1>, //preprocessed contributions for pssk_q1
    q2_coms : Vec<G1>, //preprocessed contributions for pssk_q2
}

struct VerifierPreprocessing {
    n: usize, //size of the committee as a power of 2
    g_0: G1, //first element from the KZG SRS over G1
    h_0: G2, //first element from the KZG SRS over G2
    h_1: G2, //2nd element from the KZG SRS over G2
    l_n_minus_1_of_x_com: G1,
    w_of_x_com: G1,
    sk_of_x_com: G2, //commitment to the sigma_{i \in [N]} sk_i l_i(x) polynomial
    vanishing_com: G2, //commitment to Z(x) = x^n - 1
    x_monomial_com: G2 //commentment to f(x) = x
}

struct Cache {
    lagrange_polynomials: Vec<DensePolynomial<F>>
}

fn sample_weights(n: usize) -> Vec<F> {
    let mut rng = &mut test_rng();
    (0..n).map(|_| F::from(u64::rand(&mut rng))).collect()
}

/// n is the size of the bitmap, and probability is for true or 1.
fn sample_bitmap(n: usize, probability: f64) -> Vec<F> {
    let rng = &mut test_rng();
    let mut bitmap = vec![];
    for _i in 0..n {
        //let r = u64::rand(&mut rng);
        let bit = rng.gen_bool(probability);
        bitmap.push(F::from(bit));
    }
    bitmap
}

fn prepare_cache(n: usize) -> Cache {
    let mut lagrange_polynomials = vec![];
    for i in 0..n {
        let l_i_of_x = utils::lagrange_poly(n, i);
        lagrange_polynomials.push(l_i_of_x);
    }
    Cache { lagrange_polynomials }
} 

fn main() {
    let n = 64;
    println!("n = {}", n);

    //contains commonly used objects such as lagrange polynomials
    let cache = prepare_cache(n);

    // -------------- sample one-time SRS ---------------
    //run KZG setup
    let rng = &mut test_rng();
    let params = KZG::setup(n, rng).expect("Setup failed");

    // -------------- sample universe specific values ---------------
    //sample random keys
    let sk: Vec<F> = sample_secret_keys(n - 1);
    //sample random weights for each party
    let weights = sample_weights(n - 1);

    // -------------- perform universe setup ---------------
    //run universe setup
    let (vp,pp) = setup(n, &params, &weights, &sk);

    // -------------- sample proof specific values ---------------
    //samples n-1 random bits
    let bitmap = sample_bitmap(n - 1, 0.9);

    let start = Instant::now();
    let π = prove(&params, &pp, &cache, &weights, &bitmap);
    let duration = start.elapsed();
    println!("Time elapsed in prover is: {:?}", duration);
    

    let start = Instant::now();
    verify(&vp, &π);
    let duration = start.elapsed();
    println!("Time elapsed in verifier is: {:?}", duration);
}

fn setup(
    n: usize,
    params: &UniversalParams<Bls12_381>,
    weights: &Vec<F>,
    sk: &Vec<F>
) -> (VerifierPreprocessing, ProverPreprocessing)
{
    let mut weights = weights.clone();
    let mut sk = sk.clone();

    //last element must be 0
    sk.push(F::from(0));
    weights.push(F::from(0));

    let w_of_x = compute_poly(&weights);
    let w_of_x_com = KZG::commit_g1(&params, &w_of_x).unwrap();

    //allocate space to collect setup material from all n-1 parties
    let mut q1_contributions : Vec<Vec<G1>> = vec![];
    let mut q2_contributions : Vec<G1> = vec![];
    let mut pks : Vec<G1> = vec![];
    let mut com_sks: Vec<G2> = vec![];
    
    //collect the setup phase material from all parties
    let all_parties_setup = crossbeam::scope(|s| {
        let mut threads = Vec::new();
        for i in 0..n {
            let idx = i.clone();
            let n = n.clone();
            let sk = sk[idx];
            let thread_i = s.spawn(move |_| party_i_setup_material(&params, n, idx, &sk));
            threads.push(thread_i);
        }

        threads.into_iter().map(|t| t.join().unwrap()).collect::<Vec<_>>()
    }).unwrap();

    for (pk_i, com_sk_l_i, q1_i, q2_i) in all_parties_setup {
        q1_contributions.push(q1_i.clone());
        q2_contributions.push(q2_i.clone());
        pks.push(pk_i.clone());
        com_sks.push(com_sk_l_i.clone());
    }

    let z_of_x = utils::compute_vanishing_poly(n);
    let x_monomial = utils::compute_x_monomial();
    let l_n_minus_1_of_x = utils::lagrange_poly(n, n-1);

    let vp = VerifierPreprocessing {
        n: n,
        g_0: params.powers_of_g[0].clone(),
        h_0: params.powers_of_h[0].clone(),
        h_1: params.powers_of_h[1].clone(),
        l_n_minus_1_of_x_com: KZG::commit_g1(&params, &l_n_minus_1_of_x).unwrap(),
        w_of_x_com: w_of_x_com,
        // combine all sk_i l_i_of_x commitments to get commitment to sk(x)
        sk_of_x_com: add_all_g2(&params, &com_sks),
        vanishing_com: KZG::commit_g2(&params, &z_of_x).unwrap(),
        x_monomial_com: KZG::commit_g2(&params, &x_monomial).unwrap(),
    };

    let pp = ProverPreprocessing {
        n: n,
        pks: pks,
        q1_coms: preprocess_q1_contributions(&q1_contributions),
        q2_coms: q2_contributions,
    };

    (vp, pp)

}


fn prove(
    params: &UniversalParams<Bls12_381>,
    pp: &ProverPreprocessing,
    cache: &Cache,
    weights: &Vec<F>, 
    bitmap: &Vec<F>) -> Proof {
    // compute the nth root of unity
    let n = pp.n;

    //adjust the weights and bitmap polynomials
    let mut weights = weights.clone();
    //compute sum of weights of active signers
    let total_active_weight = bitmap
        .iter()
        .zip(weights.iter())
        .fold(F::from(0), |acc, (&x, &y)| acc + (x * y));
    //weight's last element must the additive inverse of active weight
    weights.push(F::from(0) - total_active_weight);

    let mut bitmap = bitmap.clone();
    //bitmap's last element must be 1 for our scheme
    bitmap.push(F::from(1));

    let mut rng = test_rng();
    let r = F::rand(&mut rng);

    //compute all the scalars we will need in the prover
    let domain = Radix2EvaluationDomain::<F>::new(n as usize).unwrap();
    let ω: F = domain.group_gen;
    let r_div_ω: F = r / ω;
    let ω_inv: F = F::from(1) / ω;

    //compute all the polynomials we will need in the prover
    let z_of_x = utils::compute_vanishing_poly(n); //returns Z(X) = X^n - 1
    let l_n_minus_1_of_x = utils::lagrange_poly(n, n-1);
    let w_of_x = compute_poly(&weights);
    let b_of_x = compute_poly(&bitmap);
    let psw_of_x = compute_psw_poly(&weights, &bitmap);
    let psw_of_x_div_ω = utils::poly_domain_mult_ω(&psw_of_x, &ω_inv);


    //ParSumW(X) = ParSumW(X/ω) + W(X) · b(X) + Z(X) · Q1(X)
    let t_of_x = psw_of_x.sub(&psw_of_x_div_ω).sub(&w_of_x.mul(&b_of_x));
    let psw_wff_q_of_x = t_of_x.div(&z_of_x);

    //L_{n−1}(X) · ParSumW(X) = Z(X) · Q2(X) 
    let t_of_x = l_n_minus_1_of_x.mul(&psw_of_x);
    let psw_check_q_of_x = t_of_x.div(&z_of_x);

    //b(X) · b(X) − b(X) = Z(X) · Q3(X)
    let t_of_x = b_of_x.mul(&b_of_x).sub(&b_of_x);
    let b_wff_q_of_x = t_of_x.div(&z_of_x);

    //L_{n−1}(X) · (b(X) - 1) = Z(X) · Q4(X)
    let t_of_x = l_n_minus_1_of_x.clone().mul(
        &b_of_x.clone().sub(&utils::compute_constant_poly(&F::from(1))));
    let b_check_q_of_x = t_of_x.div(&z_of_x);

    let sk_q1_com = filter_and_add(&params, &pp.q1_coms, &bitmap);
    let sk_q2_com = filter_and_add(&params, &pp.q2_coms, &bitmap);
    let agg_pk = compute_apk(&pp, &bitmap, &cache);

    let psw_of_r_proof = KZG::compute_opening_proof(&params, &psw_of_x, &r).unwrap();
    let w_of_r_proof = KZG::compute_opening_proof(&params, &w_of_x, &r).unwrap();
    let b_of_r_proof = KZG::compute_opening_proof(&params, &b_of_x, &r).unwrap();
    let psw_wff_q_of_r_proof = KZG::compute_opening_proof(&params, &psw_wff_q_of_x, &r).unwrap();
    let psw_check_q_of_r_proof = KZG::compute_opening_proof(&params, &psw_check_q_of_x, &r).unwrap();
    let b_wff_q_of_r_proof = KZG::compute_opening_proof(&params, &b_wff_q_of_x, &r).unwrap();
    let b_check_q_of_r_proof = KZG::compute_opening_proof(&params, &b_check_q_of_x, &r).unwrap();

    let merged_proof: G1 = (psw_of_r_proof
        + w_of_r_proof.mul(r.pow([1]))
        + b_of_r_proof.mul(r.pow([2]))
        + psw_wff_q_of_r_proof.mul(r.pow([3]))
        + psw_check_q_of_r_proof.mul(r.pow([4]))
        + b_wff_q_of_r_proof.mul(r.pow([5]))
        + b_check_q_of_r_proof.mul(r.pow([6]))).into();

    Proof {
        agg_pk: agg_pk.clone(),
        agg_weight: total_active_weight,

        r,
        
        psw_of_r_div_ω: psw_of_x.evaluate(&r_div_ω),
        psw_of_r_div_ω_proof: KZG::compute_opening_proof(&params, &psw_of_x, &r_div_ω).unwrap(),

        psw_of_r: psw_of_x.evaluate(&r),
        w_of_r: w_of_x.evaluate(&r),
        b_of_r: b_of_x.evaluate(&r),
        psw_wff_q_of_r: psw_wff_q_of_x.evaluate(&r),
        psw_check_q_of_r: psw_check_q_of_x.evaluate(&r),
        b_wff_q_of_r: b_wff_q_of_x.evaluate(&r),
        b_check_q_of_r: b_check_q_of_x.evaluate(&r),
        
        merged_proof: merged_proof.into(),

        psw_of_x_com: KZG::commit_g1(&params, &psw_of_x).unwrap(),
        b_of_x_com: KZG::commit_g1(&params, &b_of_x).unwrap(),
        psw_wff_q_of_x_com: KZG::commit_g1(&params, &psw_wff_q_of_x).unwrap(),
        psw_check_q_of_x_com: KZG::commit_g1(&params, &psw_check_q_of_x).unwrap(),
        b_wff_q_of_x_com: KZG::commit_g1(&params, &b_wff_q_of_x).unwrap(),
        b_check_q_of_x_com: KZG::commit_g1(&params, &b_check_q_of_x).unwrap(),

        sk_q1_com: sk_q1_com,
        sk_q2_com: sk_q2_com,
    }
}

fn verify_opening(
    vp: &VerifierPreprocessing, 
    commitment: &G1,
    point: &F, 
    evaluation: &F,
    opening_proof: &G1) {
    let eval_com: G1 = vp.g_0.clone().mul(evaluation).into();
    let point_com: G2 = vp.h_0.clone().mul(point).into();

    let lhs = <Bls12_381 as Pairing>::pairing(commitment.clone() - eval_com, vp.h_0);
    let rhs = <Bls12_381 as Pairing>::pairing(opening_proof.clone(), vp.h_1 - point_com);
    assert_eq!(lhs, rhs);
}

fn verify_openings(vp: &VerifierPreprocessing, π: &Proof) {
    //adjust the w_of_x_com
    let adjustment = F::from(0) - π.agg_weight;
    let adjustment_com = vp.l_n_minus_1_of_x_com.mul(adjustment);
    let w_of_x_com: G1 = (vp.w_of_x_com + adjustment_com).into();

    let psw_of_r_argument = π.psw_of_x_com - vp.g_0.clone().mul(π.psw_of_r).into_affine();
    let w_of_r_argument = w_of_x_com - vp.g_0.clone().mul(π.w_of_r).into_affine();
    let b_of_r_argument = π.b_of_x_com - vp.g_0.clone().mul(π.b_of_r).into_affine();
    let psw_wff_q_of_r_argument = π.psw_wff_q_of_x_com - vp.g_0.clone().mul(π.psw_wff_q_of_r).into_affine();
    let psw_check_q_of_r_argument = π.psw_check_q_of_x_com - vp.g_0.clone().mul(π.psw_check_q_of_r).into_affine();
    let b_wff_q_of_r_argument = π.b_wff_q_of_x_com - vp.g_0.clone().mul(π.b_wff_q_of_r).into_affine();
    let b_check_q_of_r_argument = π.b_check_q_of_x_com - vp.g_0.clone().mul(π.b_check_q_of_r).into_affine();

    let merged_argument: G1 = (psw_of_r_argument
        + w_of_r_argument.mul(π.r.pow([1]))
        + b_of_r_argument.mul(π.r.pow([2]))
        + psw_wff_q_of_r_argument.mul(π.r.pow([3]))
        + psw_check_q_of_r_argument.mul(π.r.pow([4]))
        + b_wff_q_of_r_argument.mul(π.r.pow([5]))
        + b_check_q_of_r_argument.mul(π.r.pow([6]))).into_affine();

    let lhs = <Bls12_381 as Pairing>::pairing(
        merged_argument, 
        vp.h_0);
    let rhs = <Bls12_381 as Pairing>::pairing(
        π.merged_proof, 
        vp.h_1 - vp.h_0.clone().mul(π.r).into_affine());
    assert_eq!(lhs, rhs);

    let domain = Radix2EvaluationDomain::<F>::new(vp.n as usize).unwrap();
    let ω: F = domain.group_gen;
    let r_div_ω: F = π.r / ω;
    verify_opening(vp, &π.psw_of_x_com, &r_div_ω, &π.psw_of_r_div_ω, &π.psw_of_r_div_ω_proof);
}

fn verify(vp: &VerifierPreprocessing, π: &Proof) {
    let domain = Radix2EvaluationDomain::<F>::new(vp.n as usize).unwrap();
    let ω: F = domain.group_gen;

    verify_openings(vp, π);

    let n: u64 = vp.n as u64;
    let vanishing_of_r: F = π.r.pow([n]) - F::from(1);

    // compute L_i(r) using the relation L_i(x) = Z_V(x) / ( Z_V'(x) (x - ω^i) )
    // where Z_V'(x)^-1 = x / N for N = |V|.
    let ω_pow_n_minus_1 = ω.pow([n-1]);
    let l_n_minus_1_of_r = (ω_pow_n_minus_1 / F::from(n)) * (vanishing_of_r / (π.r - ω_pow_n_minus_1));

    //assert polynomial identity for the secret part
    let lhs = <Bls12_381 as Pairing>::pairing(&π.b_of_x_com, &vp.sk_of_x_com);
    let x1 = <Bls12_381 as Pairing>::pairing(&π.sk_q1_com, &vp.vanishing_com);
    let x2 = <Bls12_381 as Pairing>::pairing(&π.sk_q2_com, &vp.x_monomial_com);
    let x3 = <Bls12_381 as Pairing>::pairing(&π.agg_pk, &vp.h_0);
    let rhs = x1.add(x2).add(x3);
    assert_eq!(lhs, rhs);

    //assert checks on the public part

    //ParSumW(r) − ParSumW(r/ω) − W(r) · b(r) = Q(r) · (r^n − 1)
    let lhs = π.psw_of_r - π.psw_of_r_div_ω - π.w_of_r * π.b_of_r;
    let rhs = π.psw_wff_q_of_r * vanishing_of_r;
    assert_eq!(lhs, rhs);

    //Ln−1(X) · ParSumW(X) = Z(X) · Q2(X)
    //TODO: compute l_n_minus_1_of_r in verifier -- dont put it in the proof.
    let lhs = l_n_minus_1_of_r * π.psw_of_r;
    let rhs = vanishing_of_r * π.psw_check_q_of_r;
    assert_eq!(lhs, rhs);

    //b(r) * b(r) - b(r) = Q(r) · (r^n − 1)
    let lhs = π.b_of_r * π.b_of_r - π.b_of_r;
    let rhs = π.b_wff_q_of_r * vanishing_of_r;
    assert_eq!(lhs, rhs);

    //Ln−1(X) · (b(X) − 1) = Z(X) · Q4(X)
    let lhs = l_n_minus_1_of_r * (π.b_of_r - F::from(1));
    let rhs = vanishing_of_r * π.b_check_q_of_r;
    assert_eq!(lhs, rhs);

}


fn compute_apk(
    pp: &ProverPreprocessing, 
    bitmap: &Vec<F>,
    cache: &Cache) -> G1 {
    let n = bitmap.len();
    let mut exponents = vec![];
    for i in 0..n {
        //let l_i_of_x = utils::lagrange_poly(n, i);
        let l_i_of_x = cache.lagrange_polynomials[i].clone();
        let l_i_of_0 = l_i_of_x.evaluate(&F::from(0));
        let active = bitmap[i] == F::from(1);
        exponents.push(if active { l_i_of_0 } else { F::from(0) });
    }

    <<Bls12_381 as Pairing>::G1 as VariableBaseMSM>
        ::msm(&pp.pks[..], &exponents).unwrap().into_affine()
}

fn preprocess_q1_contributions(
    q1_contributions: &Vec<Vec<G1>>
) -> Vec<G1> {
    let n = q1_contributions.len();
    let mut q1_coms = vec![];

    for i in 0..n {
        let mut party_i_q1_com = q1_contributions[i][i].clone();
        for j in 0..n {
            if i != j {
                let party_j_contribution = q1_contributions[j][i].clone();
                party_i_q1_com = party_i_q1_com.add(party_j_contribution).into();
            }
        }
        q1_coms.push(party_i_q1_com);
    }
    q1_coms
}

fn filter_and_add(
    params: &UniversalParams<Bls12_381>, 
    elements: &Vec<G1>, 
    bitmap: &Vec<F>) -> G1 {
    let mut com = get_zero_poly_com_g1(&params);
    for i in 0..bitmap.len() {
        if bitmap[i] == F::from(1) {
            com = com.add(elements[i]).into_affine();
        }
    }
    com
}

fn add_all_g2(
    params: &UniversalParams<Bls12_381>, 
    elements: &Vec<G2>) -> G2 {
    let mut com = get_zero_poly_com_g2(&params);
    for i in 0..elements.len() {
        com = com.add(elements[i]).into_affine();
    }
    com
}

fn get_zero_poly_com_g1(params: &UniversalParams<Bls12_381>) -> G1 {
    let zero_poly = utils::compute_constant_poly(&F::from(0));
    KZG::commit_g1(&params, &zero_poly).unwrap()
}

fn get_zero_poly_com_g2(params: &UniversalParams<Bls12_381>) -> G2 {
    let zero_poly = utils::compute_constant_poly(&F::from(0));
    KZG::commit_g2(&params, &zero_poly).unwrap()
}

fn sample_secret_keys(num_parties: usize) -> Vec<F> {
    let mut rng = test_rng();
    let mut keys = vec![];
    for _ in 0..num_parties {
        keys.push(F::rand(&mut rng));
    }
    keys
}

fn compute_poly(v: &Vec<F>) -> DensePolynomial<F> {
    let n = v.len();
    let mut evals = vec![];
    for i in 0..n {
        evals.push(v[i]);
    }

    let domain = Radix2EvaluationDomain::<F>::new(n).unwrap();
    let eval_form = Evaluations::from_vec_and_domain(evals, domain);
    eval_form.interpolate()
}

fn compute_psw_poly(weights: &Vec<F>, bitmap: &Vec<F>) -> DensePolynomial<F> {
    let n = weights.len();
    let mut parsum = F::from(0);
    let mut evals = vec![];
    for i in 0..n {
        let w_i_b_i = bitmap[i] * weights[i];
        parsum += w_i_b_i;
        evals.push(parsum);
    }

    let domain = Radix2EvaluationDomain::<F>::new(n).unwrap();
    let eval_form = Evaluations::from_vec_and_domain(evals, domain);
    eval_form.interpolate()    
}

fn party_i_setup_material(
    params: &UniversalParams<Bls12_381>,
    n: usize, 
    i: usize, 
    sk_i: &F) -> (G1, G2, Vec<G1>, G1) {
    //let us compute the q1 term
    let l_i_of_x = utils::lagrange_poly(n, i);
    let z_of_x = utils::compute_vanishing_poly(n);

    let mut q1_material = vec![];
    //let us compute the cross terms of q1
    for j in 0..n {
        let num: DensePolynomial<F>;// = compute_constant_poly(&F::from(0));
        if i == j {
            num = l_i_of_x.clone().mul(&l_i_of_x).sub(&l_i_of_x);
        } else { //cross-terms
            let l_j_of_x = utils::lagrange_poly(n, j);
            num = l_j_of_x.mul(&l_i_of_x);
        }
        let f = num.div(&z_of_x);
        let sk_times_f = utils::poly_eval_mult_c(&f, &sk_i);

        let com = KZG::commit_g1(&params, &sk_times_f)
            .expect("commitment failed");

        q1_material.push(com);
    }

    let x_monomial = utils::compute_x_monomial();
    let l_i_of_0 = l_i_of_x.evaluate(&F::from(0));
    let l_i_of_0_poly = utils::compute_constant_poly(&l_i_of_0);
    let num = l_i_of_x.sub(&l_i_of_0_poly);
    let den = x_monomial.clone();
    let f = num.div(&den);
    let sk_times_f = utils::poly_eval_mult_c(&f, &sk_i);
    let q2_com = KZG::commit_g1(&params, &sk_times_f).expect("commitment failed");

    //release my public key
    let sk_as_poly = utils::compute_constant_poly(&sk_i);
    let pk = KZG::commit_g1(&params, &sk_as_poly).expect("commitment failed");

    let sk_times_l_i_of_x = utils::poly_eval_mult_c(&l_i_of_x, &sk_i);
    let com_sk_l_i = KZG::commit_g2(&params, &sk_times_l_i_of_x).expect("commitment failed");

    (pk, com_sk_l_i, q1_material, q2_com)
}


#[cfg(test)]
mod tests {
    use super::*;

    fn aggregate_sk(sk: &Vec<F>, bitmap: &Vec<F>) -> F {
        let n = sk.len();
        let mut agg_sk = F::from(0);
        for i in 0..sk.len() {
            let l_i_of_x = utils::lagrange_poly(n, i);
            let l_i_of_0 = l_i_of_x.evaluate(&F::from(0));
            agg_sk += bitmap[i] * sk[i] * l_i_of_0;
        }
        agg_sk
    }

    fn sanity_test_poly_domain_mult(
        f_of_x: &DensePolynomial<F>, 
        f_of_ωx: &DensePolynomial<F>, 
        ω: &F) {
        let mut rng = test_rng();
        let r = F::rand(&mut rng);
        let ωr: F = ω.clone() * r;
        assert_eq!(f_of_x.evaluate(&ωr), f_of_ωx.evaluate(&r));
    }

    fn sanity_test_b(
        b_of_x: &DensePolynomial<F>,
        q_of_x: &DensePolynomial<F>
    ) {
    
        let mut rng = test_rng();
        let r = F::rand(&mut rng);
    
        let n: u64 = (b_of_x.degree() + 1) as u64;
    
        let b_of_r = b_of_x.evaluate(&r);
        let q_of_r = q_of_x.evaluate(&r);
        let vanishing_of_r: F = r.pow([n]) - F::from(1);
    
        //ParSumW(ωr) − ParSumW(r) − W(ωr) · b(ωr) = Q2(r) · (r^n − 1)
        let left = b_of_r * b_of_r - b_of_r;
        let right = q_of_r * vanishing_of_r;
        //println!("ParSumW(ωr) - ParSumW(r) - W(ωr)·b(ωr) = {:?}", tmp1);
        //println!("Q(r) · (r^n - 1) = {:?}", tmp2);
        assert_eq!(left, right);
    
    }
    
    fn sanity_test_psw(
        w_of_x: &DensePolynomial<F>,
        b_of_x: &DensePolynomial<F>,
        psw_of_x: &DensePolynomial<F>,
        q_of_x: &DensePolynomial<F>
    ) {
    
        let mut rng = test_rng();
        let r = F::rand(&mut rng);
    
        let n: u64 = (b_of_x.degree() + 1) as u64;
        let domain = Radix2EvaluationDomain::<F>::new(n as usize).unwrap();
        let ω: F = domain.group_gen;
        let ω_pow_n_minus_1: F = ω.pow([n-1]);
        let ωr: F = ω * r;
    
        let psw_of_r = psw_of_x.evaluate(&r);
        let psw_of_ωr = psw_of_x.evaluate(&ωr);
        let w_of_ωr = w_of_x.evaluate(&ωr);
        let b_of_ωr = b_of_x.evaluate(&ωr);
        let q_of_r = q_of_x.evaluate(&r);
        let vanishing_of_r: F = r.pow([n]) - F::from(1);
    
        //ParSumW(ωr) − ParSumW(r) − W(ωr) · b(ωr) = Q2(r) · (r^n − 1)
        let tmp1 = psw_of_ωr - psw_of_r - w_of_ωr * b_of_ωr;
        let tmp2 = q_of_r * vanishing_of_r;
        //println!("ParSumW(ωr) - ParSumW(r) - W(ωr)·b(ωr) = {:?}", tmp1);
        //println!("Q(r) · (r^n - 1) = {:?}", tmp2);
        assert_eq!(tmp1, tmp2);
    
        //ParSumW(ωn−1) = 0
        let psw_of_ω_pow_n_minus_1 = psw_of_x.evaluate(&ω_pow_n_minus_1);
        //println!("ParSumW(ω^(n-1)) = {:?}", psw_of_ω_pow_n_minus_1);
        assert_eq!(psw_of_ω_pow_n_minus_1, F::from(0));
    
        //b(ωn−1) = 1
        let b_of_ω_pow_n_minus_1 = b_of_x.evaluate(&ω_pow_n_minus_1);
        assert_eq!(b_of_ω_pow_n_minus_1, F::from(1));
    
    }

    #[test]
    fn sanity_test_public_part() {
        // compute the nth root of unity
        //println!("The nth root of unity is: {:?}", ω);
        //println!("The omega_n_minus_1 of unity is: {:?}", ω.pow([n-1]));
        //println!("The omega_n of unity is: {:?}", ω_pow_n_minus_1 * ω);

        let weights: Vec<F> = vec![
            F::from(2), 
            F::from(3), 
            F::from(4), 
            F::from(5), 
            F::from(4), 
            F::from(3), 
            F::from(2), 
            F::from(0)-F::from(15)
        ];
        let bitmap: Vec<F> = vec![
            F::from(1),
            F::from(1), 
            F::from(0), 
            F::from(1), 
            F::from(0), 
            F::from(1), 
            F::from(1), 
            F::from(1)
        ];

        let n: u64 = bitmap.len() as u64;
        let domain = Radix2EvaluationDomain::<F>::new(n as usize).unwrap();
        let ω: F = domain.group_gen;

        let w_of_x = compute_poly(&weights);
        let w_of_ωx = utils::poly_domain_mult_ω(&w_of_x, &ω);

        let b_of_x = compute_poly(&bitmap);
        let b_of_ωx = utils::poly_domain_mult_ω(&b_of_x, &ω);

        let psw_of_x = compute_psw_poly(&weights, &bitmap);
        let psw_of_ωx = utils::poly_domain_mult_ω(&psw_of_x, &ω);

        //t(X) = ParSumW(ω · X) − ParSumW(X) − W(ω · X) · b(ω · X)
        let t_of_x = psw_of_ωx.sub(&psw_of_x).sub(&w_of_ωx.mul(&b_of_ωx));
        let z_of_x = utils::compute_vanishing_poly(n); //returns Z(X) = X^n - 1
        let q2_of_x = t_of_x.div(&z_of_x);

        let t_of_x = b_of_x.mul(&b_of_x).sub(&b_of_x);
        let q1_of_x = t_of_x.div(&z_of_x);
        
        sanity_test_poly_domain_mult(&w_of_x, &w_of_ωx, &ω);
        sanity_test_poly_domain_mult(&b_of_x, &b_of_ωx, &ω);
        sanity_test_poly_domain_mult(&psw_of_x, &psw_of_ωx, &ω);

        sanity_test_psw(&w_of_x, &b_of_x, &psw_of_x, &q2_of_x);
        sanity_test_b(&b_of_x, &q1_of_x);
    }

    fn sanity_test_pssk(
        sk_of_x: &DensePolynomial<F>,
        b_of_x: &DensePolynomial<F>,
        q1_of_x: &DensePolynomial<F>,
        q2_of_x: &DensePolynomial<F>,
        agg_sk: &F
    ) {
        let mut rng = test_rng();
        let r = F::rand(&mut rng);
        let n: u64 = (sk_of_x.degree() + 1) as u64;

        //SK(x) · B(x) − aSK = Q1(x) · Z(x) + Q2(x) · x
        let sk_of_r = sk_of_x.evaluate(&r);
        let b_of_r = b_of_x.evaluate(&r);
        let q1_of_r = q1_of_x.evaluate(&r);
        let z_of_r: F = r.pow([n]) - F::from(1);
        let q2_of_r = q2_of_x.evaluate(&r);

        let left = sk_of_r * b_of_r;
        let right = (q1_of_r * z_of_r) + (q2_of_r * r) + agg_sk;
        assert_eq!(left, right);
    
    }

    #[test]
    fn sanity_test_secret_part() {
        //let weights: Vec<u64> = vec![2, 3, 4, 5, 4, 3, 2];
        let bitmap: Vec<F> = vec![
            F::from(1),
            F::from(1), 
            F::from(0), 
            F::from(1), 
            F::from(0), 
            F::from(1), 
            F::from(1), 
            F::from(1)
        ];

        let n = bitmap.len();

        let mut secret_keys: Vec<F> = sample_secret_keys(n - 1);
        secret_keys.push(F::from(0));

        let agg_sk = aggregate_sk(&secret_keys, &bitmap);
        println!("agg_sk = {:?}", agg_sk);
        let sk_of_x = compute_poly(&secret_keys);
        let b_of_x = compute_poly(&bitmap);
        let q1_of_x = compute_pssk_q1_poly(&secret_keys, &bitmap);
        let q2_of_x = compute_pssk_q2_poly(&secret_keys, &bitmap);

        sanity_test_pssk(&sk_of_x, &b_of_x, &q1_of_x, &q2_of_x, &agg_sk);
    }

    fn compute_pssk_q1_poly(
        sk: &Vec<F>, 
        bitmap: &Vec<F>
    ) -> DensePolynomial<F> {
        let n = sk.len();
        let z_of_x = utils::compute_vanishing_poly(n as u64);
        //Li(x) · Li(x) − Li(x) / Z(x)
        let mut q1 = utils::compute_constant_poly(&F::from(0));

        for i in 0..n {
            if bitmap[i] == F::from(0) { continue; }

            let l_i_of_x = utils::lagrange_poly(n, i);
            let num = l_i_of_x.mul(&l_i_of_x).sub(&l_i_of_x);
            //let num = num.sub(&l_i_of_x);
            let f_i = num.div(&z_of_x);
            let sk_i_f_i = utils::poly_eval_mult_c(&f_i, &sk[i]);

            q1 = q1.add(sk_i_f_i);

            let mut q1_inner = utils::compute_constant_poly(&F::from(0));
            for j in 0..n {
                if i == j { continue; } //i != j

                let l_j_of_x = utils::lagrange_poly(n, j);
                let num = l_j_of_x.mul(&l_i_of_x);
                let f_j = num.div(&z_of_x);
                let sk_j_f_j = utils::poly_eval_mult_c(&f_j, &sk[j]);

                q1_inner = q1_inner.add(sk_j_f_j);
            }

            q1 = q1.add(q1_inner);
        }
        q1
    }

    fn compute_pssk_q2_poly(
        sk: &Vec<F>, 
        bitmap: &Vec<F>
    ) -> DensePolynomial<F> {
        let n = sk.len();
        let x_monomial = utils::compute_x_monomial();

        let mut q2 = utils::compute_constant_poly(&F::from(0));

        for i in 0..n {
            if bitmap[i] == F::from(0) { continue; }

            let l_i_of_x = utils::lagrange_poly(n, i);
            let l_i_of_0 = l_i_of_x.evaluate(&F::from(0));
            let l_i_of_0 = utils::compute_constant_poly(&l_i_of_0);
            let num = l_i_of_x.sub(&l_i_of_0);
            let den = x_monomial.clone();
            let f_i = num.div(&den);
            let sk_i_f_i = utils::poly_eval_mult_c(&f_i, &sk[i]);

            q2 = q2.add(sk_i_f_i);
        }
        q2
    }

}
