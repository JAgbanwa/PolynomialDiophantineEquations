import cypari2
pari = cypari2.Pari(); pari.allocatemem(10**9)
B = 1500000
N = pari('2*x^3-8*x^2-3'); dN = pari('6*x^2-16*x')
out = open('nbad.txt','w'); cnt = 0; nbadroots = 0
for p in pari.primes([5, B]):
    p = int(p)
    for th in pari.polrootsmod(N, p):
        th = int(pari.lift(th))
        if (th*(2*th-1)) % p == 0: continue          # p | 2a(2a-1): skip
        if (6*th*th - 16*th) % p == 0: continue      # multiple root: skip (no unique lift)
        if pari.kronecker(-2*th*(2*th-1), p) != -1: continue
        # Hensel lift theta to mod p^2
        p2 = p*p
        t2 = (th - (2*th**3 - 8*th**2 - 3) * pow(6*th*th - 16*th, -1, p2)) % p2
        assert (2*t2**3 - 8*t2**2 - 3) % p2 == 0
        out.write(f"{p} {th} {t2}\n"); nbadroots += 1
print("bad roots written:", nbadroots)
