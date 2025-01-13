# Lambdaworks Baby SNARK

An implementation of [Baby SNARK](https://github.com/initc3/babySNARK/blob/bebb2948f8094a8d3949afe6d10b89a120a005be/babysnark.pdf) protocol.

# Example

Below is a simple example demonstrating the usage of BabySnark:

**Step 1:** Construct Span Program (ssp):

```rust
    // Define Constraint Matrix 
    let u = vec![
        i64_vec_to_field(&[-1, 2, 0, 0]),
        i64_vec_to_field(&[-1, 0, 2, 0]),
        i64_vec_to_field(&[-1, 0, 0, 2]),
        i64_vec_to_field(&[-1, 2, 2, -4]),
    ];
    let witness = i64_vec_to_field(&[1, 1, 1]);
    let public = i64_vec_to_field(&[1]);
    let mut input = public.clone();
    input.extend(witness.clone());
    // Construct Span Program (ssp):
    let ssp = SquareSpanProgram::from_scs(SquareConstraintSystem::from_matrix(u, public.len()));
```

*Note:* You must ensure that the first element of the `input` is 1. In the code above we can see how to build a Span Program for an And Gate. There, the variable `witness` is of the form `[input_1, input_2, output]` (which satisfy `input_1 ∧ input_2 = output`) and the `public` variable must be `[1]`.

**Step 2:** Setup Proving and Verification Keys:
```rust
    let (pk, vk) = setup(&ssp);
```
**Step 3:** The prover generates a proof using the input, the SSP, and the proving key.
```rust
    let proof = Prover::prove(&input, &ssp, &pk);
```
**Step 4:** The verifier checks the validity of the proof using the verification key and the public input.
```rust
    let verified = verify(&vk, &proof, &public);
    assert!(verified);
```

# Working principle

## Programs as relationships between polynomials

BabySNARK is based on this [NIZK](https://eprint.iacr.org/2014/718) proposed in 2014. It works with square span programs, which are similar to, yet simpler than, quadratic arithmetic programs (used in [Pinocchio](https://eprint.iacr.org/2013/279)). The representation of the circuit is done with a matrix $U$ (belonging to $F^{m \times n}$) and a vector $z = (1 , u , w)^t$ (containing the instance $u$ and witness $w$),
$(U.z) \circ (U.z) = 1$

We can express any boolean circuit using these types of constraints. Let us rewrite the equations in a different form that will be convenient for later purposes:
$\left(\sum_j u_{ij} z_j \right)^2 = 1$
which should be valid for every $i = 0, 1, 2, ...$. We can encode these equations using polynomials. Suppose that $m = 2^k$ for some $k$ and that we are working with a nice field $F$ containing a subgroup $D_i$ of size $2^k$. We can take $\omega$ as an $m$-th primitive root of unity ($\omega$ generates the whole subgroup) and find the polynomials $U_j (x)$ which satisfy 
$U_j (\omega^i ) = u_{ij}$
By doing this, we are encoding our equations as relations over polynomials. Thus, we can replace the problem equivalently,
$\left(\sum_j U_{j} (x) z_j \right)^2 - 1 = p(x)$
If we evaluate the polynomials at $\omega^i$, then we get $U_j (\omega^i ) = u_{ij}$, and $p(\omega^i )$ evaluates to $0$ at every $\omega^i$. A theorem says that if $\omega^i$ is a root/zero of a polynomial $p(x)$, then $x - \omega^i$ divides $p(x)$. In other words, there is some $q (x)$ such that $p(x) = (x - \omega^i )q(x)$.

If the polynomial has multiple zeros, then it must be divisible by each $x - \omega^i$. Let us define $Z(x)$ as the vanishing polynomial over $D_i$
$Z(x) = \prod_j (x -\omega^j ) = x^m - 1$
where we used in the last equality that $\omega$ is a primitive $m$-th root of unity (this trick is also used in [STARKs](https://blog.lambdaclass.com/diving-deep-fri/)). Therefore, if all the constraints hold, we have a polynomial $q(x)$ which fulfills this equality
$p(x) = Z(x) q(x)$

One way to show that the computation described by the system of equations is valid is by providing $p(x)$ and $q(x)$ and letting the verifier check the equality by himself. The problem is that we have to pass all the coefficients of both polynomials (which are as long as the computation) and let him compute the right-hand side and assert whether it equals the polynomial on the left-hand side. Besides, we also leak information on the witness! How can we turn this into something succinct and not leak information?

## Polynomial commitment schemes

A polynomial commitment scheme is given by four algorithms: setup, commit, open, and evaluate. The commitment allows us to bind ourselves to a given polynomial using short data and later be able to prove things about that polynomial. The commitment scheme must satisfy the following two properties:
1. Hiding: the commitment does not reveal anything about the committed polynomial.
2. Binding: given the commitment to $p(x)$, $\mathrm{cm} (p)$, it is infeasible to find another $q(x)$, such that $\mathrm{cm} (p) = \mathrm{cm} (q)$

One way to build a PCS is by using a pairing-friendly elliptic curve, such as BN254 or BLS12-381. We will work here with type-3 pairings, which are functions $e: G_1 \times G_2 \rightarrow G_t$ with the following properties:
1. Bilinearity: $e(a g_1 , b g_2) = e(g_1 , g_2 )^{ab}$.
2. Non-degeneracy: If $e(P,Q) = 1$, then either $P = \mathcal{O}$ or $Q = \mathcal{O}$.

[KZG commitment scheme](https://blog.lambdaclass.com/mina-to-ethereum-bridge/) works in this setting, which is the tool we will use. Why are pairings useful? Because they provide us with a way of multiplying things hidden inside an elliptic curve group.

We pick a random $s$ (which is unknown to both the prover and verifier), and we generate the following points in the elliptic curve
$\\{ P_0 , P_1 , ..., P_n \\} = \\{ g_1 , s g_1 , ..., s^n g_n \\}$
These points contain the powers of $s$ hidden inside a group of the elliptic curve. Given any $P_k$, recovering $s$ is computationally intractable due to the hardness of the discrete log problem over elliptic curves.

We commit to the polynomial by computing 
$p(s) g_1 = \sum a_k (s^k g_1 ) = \sum a_k P_k$
where $g_1$ is a generator of the group/subgroup of prime order $r$ of the elliptic curve. We could also commit using elements in $G_2$, where we have $g_2$ as a subgroup generator.

Using pairings, we could prove the relationship between the polynomial $p(x)$ and the quotient $q(x)$ by computing two pairings and checking their equality:
$e( p(s) g_1 , g_2) = e(g_1 , g_2 )^{p(s)}$
$e(q(s) g_1 , s^m g_2 - g_2) = e(g_1 , g_2 )^{ q(s)(s^m - 1)}$
Since $s$ is chosen at random, if $p(s) = q(s) Z(s)$, then with overwhelming probability, we have that $p(x) = q(x) Z(x)$.

With this construction, we do not need to supply the verifier with the coefficients of the polynomials, only their commitments. This solves part of the problem but not everything.

## Intuition for the protocol

The program/circuit that we want to prove is defined by the matrix $U$. When we define a particular instance/public input $u$ to the circuit, if $u$ is valid, we should be able to find some $w$ that solves the system of equations. To make the proof succinct, we should send much less information than the full witness (besides, if we want zero-knowledge, the witness should be kept secret). 

We have the polynomial $p(x)$ of the problem, the vanishing polynomial $Z(x)$, and the quotient $q(x)$. In the end we want to prove that
$p(x) = Z(x)q(x)$
if the computation is valid. $Z(x)$ is known to both the prover and the verifier, and we could even commit to $Z(x)$ as part of the public information. We can reduce this check to just one point $x = s$ and verify this using pairings. However, this check alone would be insufficient since the prover could provide any polynomial $p(x)$. If we recall how we build $p(x)$,
$\left(\sum_j U_{j} (x) z_j \right)^2 - 1 = p(x)$
Some terms in the summation can be computed by the verifier (since these are public). However, the verifier does not know the witness's terms, and we do not want to give him access to that data in total. The solution would be for the prover to give the summation, including only the values of the witness,
$$V_w (x) = \sum_{j \in w} w_j U_j(x)$$
Moreover, we can provide a commitment to $V_w (x)$ using the commitment scheme we had before, $V_w (s) g_1$ and $V_w (s) g_2$ (we will show why we need both soon). The verifier can then compute 
$$V_u (x) = \sum_{k \in u} u_j U_j(x)$$
and get $V_u (s) g_1$ and $V_u (s) g_2$. The verifier can compute the pairing involving $e( p(s) g_1 , g_2)$ in an equivalent way,
$$e ( V_u (s) g_1 + V_w(s) g_1 , V_u (s) g_2 + V_w(s) g_2 ) e ( g_1 , g_2 )^{ - 1 } = e( p(s) g_1 , g_2)$$
This looks odd, but if we take all the scalars to the exponent, we have $(V_u (s) + V_w (s))(V_u (s) + V_w (s)) - 1$, and the verifier can get the polynomial of the circuit. So, we get the first check,
$$e ( V_u (s) g_1 + V_w(s) g_1 , V_u (s) g_2 + V_w(s) g_2 ) e ( g_1 , g_2 )^{ - 1 } = e( q(s) g_1 , Z(s)g_2)$$

We have one problem, though. How do we know that the prover used the same $V_w (x)$ in both commitments? Luckily, we can solve this with another pairing check,
$e( V_w (s) g_1 , g_2 ) = e( g_1 , V_w(s) g_2 )$

We got another check. Finally, how do we know that the verifier computed $V_w (x)$ correctly and did not do some random linear combination that will cancel out with the public input and yield something nice?

We could force the prover to provide the same linear combination, but with the points all shifted by some constant $\beta$, unknown to the parties. We define
$B_w (x) = \sum \beta w_j U_j (x) = \beta V_w (x)$
We can do one final check for this relationship using pairings,
$e( B_w (s) g_1 , \gamma g_2 ) = e( \gamma \beta g_1 , V_w (s) g_2 )$
where $\gamma$ is also unknown to the parties. This makes it impossible for the prover to build fake polynomials for $V_w (x)$. We can see that if this condition did not exist, we could create any $V_w (x) = C Z(x) - V_u (x) + 1$, which would pass all the other checks for any $C$ of our choice. In fact,
$V_w (x) + V_u (x) = C Z(x) + 1$
But $p(x) = (V_w (x) + V_u (x))^2 - 1$, so
$p(x) = C^2 Z(x)Z(x) + C Z(x) = Z(x) (C^2 Z(x) + C)$
and we find that $q(x) = (C^2 Z(x) + C)$, even though we do not know the witness.

The proof $\pi$ will consist of:
1. The commitment to $V_w (x)$ using $g_1$.
2. The commitment to $V_w (x)$ using $g_2$.
3. The commitment to the quotient polynomial $q(x)$ using $g_1$.
4. The commitment to $B_w (x)$ using $g_1$

The verification involves six pairings (the pairing $e(g_1 , g_2)^{ - 1}$ can be precomputed since it is a constant), to check the three conditions we mentioned.

To compute the commitments, we need parameters $s , \beta , \gamma$ to be unknown to both parties (hence, they are toxic waste). We need to generate a reference string, which will be circuit dependent (that is because we need to provide $\beta U_j(s) g_1$). With all this, we can jump into the implementation.

# Implementation

## Setup

Prover and verifier agree on a pairing-friendly elliptic curve and generators of the groups $G_1$ and $G_2$, denoted by $g_1$ and $g_2$, respectively. In our case, we choose BLS12-381. The proving key consists of the following:
1. $\\{s^k g_1 \\}$ for $k =  0, 1, 2 , ... m$
2. $\\{U_j (s) g_1 \\}$ for $j = l , l + 1 , ... m$ ($l$ being the number of public inputs).
3. $\\{U_j (s) g_2 \\}$ for $j = l , l + 1 , ... m$
4. $\\{\beta U_j (s) g_1 \\}$ for $j = l , l + 1 , ... m$

The verifying key consists of the following:
1. $\\{U_j (s) g_1 \\}$ for $j = 0 , 1 , ... l - 1$
2. $\\{U_j (s) g_2 \\}$ for $j = 0 , 1 , ... l - 1$
3. $[Z^\prime ] = (s^m - 1)g_2$ (commitment to the vanishing polynomial)
4. $e(g_1 , g_2)^{ - 1}$
5. $\beta \gamma g_1$
6. $\gamma g_2$

## Prove

The steps for the prover are as follows:
1. Compute $[V_w ] = V_w (s) g_1$, $[V_w^\prime ] = V_w (s) g_2$, and $[B_w ] = B_w (s) g_1$ using the proving key.
2. Compute the polynomial quotient polynomial $q(x)$ from the zerofier $Z(x)$, the vector of witness and instance, and the polynomials describing the circuit $U_j (x)$.
3. Compute $[q ] = q(s) g_1$ using the proving key.
4. Produce the proof $\pi = ( [q] , [V_w ] , [V_w^\prime ] , [B_w ])$

## Verify

The verifier has the following steps:
1. Parse the proof $\pi$ as $[q] , [V_w ] , [V_w^\prime ] , [B_w ]$.
2. Check $e( [V_w ] , g_2 ) = e( g_1 , [V_w^\prime ])$
3. Check $e( [B_w] , \gamma g_2) = e( \beta \gamma g_1 , [V_w^\prime ])$
4. Compute $[V_u ] = V_u (s) g_1$, and $[V_u^\prime ] = V_u (s) g_2$ using the verifying key.
5. Check $e([V_u ] + [V_w ] , [V_u^\prime ] + [V_w^\prime ])e(g_1 , g_2)^{ - 1} = e( [q] , [Z^\prime])$

If all checks pass, the proof is valid.

## Optimizations

1. Interpolation is done using the Fast Fourier Transform (FFT). This is possible because BLS12-381's scalar field has $2^{32}$ as one of its factors.
2. The quotient is calculated in evaluation form, using the FFT. We need to evaluate the polynomials at $\mu \omega^k$, where $\mu$ is the offset (we want to evaluate on cosets because if we evaluate directly over $D_i$, we get $0/0$).
3. The evaluation of the vanishing polynomial is straightforward: $Z(\mu \omega^k ) = (\mu \omega^k )^m - 1 = \mu^m - 1$, because $\omega$ has order $m$. 
4. Compute multiscalar multiplications using Pippenger's algorithm.

## Turning the SNARK into a zk-SNARK.

The protocol above is not zero-knowledge since $V_w (x)$ can be distinguished from a random-looking $V (x)$. To make it zero-knowledge, the prover has to sample a random value $\delta$ and make the following changes to the polynomials:
1. The polynomial $p(x) = \left(\sum_k z_j U_j(x) + \delta Z(x) \right)^2 - 1$. Note that adding $Z(x)$ does not change the main condition, which is that the constraints are satisfied if and only if $p(x)$ is divisible by $Z(x)$.
2. Compute $[V_w ] = (V_w (s) + \delta Z(s)) g_1$, $[V_w^\prime ] = (V_w (s) + \delta Z(s)) g_2$, and $[B_w ] = (B_w (s) + \beta \delta Z(s)) g_1$.

The verifier's steps are unchanged.
