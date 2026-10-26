# Coverage (d = x + y ≡ 2 mod 10, the distinguished pair)

No solutions found anywhere so far. "Candidates" are pairs (d, e) with e | N(d), sign(e) = sign(d), |e| ≤ 2.3|d| + 50.

| range of \|d\| | part | candidates tested | date (2026) |
|---|---|---|---|
| < 10⁹ | complete (all divisors) | 1.48·10⁹ | 25 Oct |
| 10⁹ – 10¹⁰ | sieve, primes ≤ 2.3·10⁹ | 1.47·10¹⁰ | 25 Oct |
| < 10¹⁰ | large primes 2.3·10⁹ < q ≤ 2.3·10¹⁰ | 1.26·10⁸ | 25 Oct |
| 10¹⁰ – 10¹¹ | sieve, primes ≤ 2.3·10⁹ | 1.589·10¹¹ | 25 Oct |
| 10¹⁰ – 10¹² | large primes 2.3·10⁹ < q ≤ 2.3·10¹¹ (9,044,642,851 primes) | 6.69·10¹⁰ | 25 Oct |

**Complete for all |d| < 10¹¹**, hence no solution with max(|x|, |y|, |z|) < 5·10¹⁰.

Remaining for |d| < 10¹³: sieve for 10¹¹ ≤ |d| < 10¹³, and large primes q ≤ 2.3·10¹³ (the large primes q ≤ 2.3·10¹¹
are already done for |d| < 10¹²). These are exactly the 656 units in `charity-engine/workunits.txt`.
A 2-core cloud run is working upward from 10¹¹ as well (complete below 1.58·10¹¹ on 26 Oct).
