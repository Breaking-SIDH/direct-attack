from sage.all import Mod, Factorization, ZZ

# see e.g. https://ia.cr/2023/106 Theorem 2
def find_smallest_extension(p, q):
    """
    Computes the smallest integer k such
    that q | # E / F_p^2k
    Returns the int k and the order n
    """
    if not q.is_prime():
        raise NotImplementedError
    pmodq = Mod(p, q)
    k = pmodq.multiplicative_order()
    if k%2 == 0 and pmodq**(k//2) == -1:
        k //= 2
        n = p**k + 1
    else:
        n = p**k - 1
    assert n % q == 0
    # assert EA.cardinality(extension_degree=k) == n
    return k, n

from xonly import xPoint
def gen_xpoint_order_q(E, q):
    """
    Given a prime q, we can find the minimum
    k such that there is a point of order q.
    Then, we can generate such a point by
    computing the extension Fpk and looking at
    E / Fpk
    To find a point of order q, we generate
    a random point on the curve and multiply by
    (n // q^2)
    If P != E(0) then it must be a point of
    order q.
    """
    if not q.is_prime():
        raise NotImplementedError

    Fp2 = E.base()
    p = Fp2.characteristic()
    k, n = find_smallest_extension(p, q)

    Fp2k = Fp2.extension(k, name="T")
    E_new = E.base_extend(Fp2k)
    print(f"DEBUG [gen_xpoint_order_q]: Needed to compute an extension of degree {k = }")

    v = n.valuation(q)
    assert v >= 1
    scalar = n.prime_to_m_part(q)
    while True:
        P = xPoint(Fp2k.random_element(), E_new)
        P = P.mul(scalar)
        # print(P)
        if not P:
            continue
        for _ in range(v):
            Q = P.mul(q)
            if not Q:
                break
            P = Q
        else:
            # not on correct twist
            continue
        break
    return P.X

from xonly import kernel_polynomial_from_x
def an_isogeny(E,q):
    """
    Compute an isogeny of prime degree q from E
    using x-only arithmetic.
    """
    EE = E.short_weierstrass_model()
    iso = E.isomorphism_to(EE)
    x = gen_xpoint_order_q(EE, q)
    kerpoly = kernel_polynomial_from_x(EE, x, q)
    return EE.isogeny(kerpoly) * iso

def divide_by(pt, d):
    """
    Finds all points P s.t. d*P == pt
    If all == False, it returns only one point
    """
    if not isinstance(d, Factorization):
        d = ZZ(d).factor()
    if not d:
        yield pt
        return
    l = d[-1][0]
    d /= l
    for pt2 in pt.division_points(l):
        yield from divide_by(pt2, d)

def find_secret_key(T, P, Q, ea):
    """
    Finds k s.t. <P+k*Q> = <T>, where T,P,Q are 3^ea-torsion points
    This is needed to retrieve the secret key in SIDH once the dual
    of the secret (partial)-isogeny is available
    """
    # Weil pairing of the basis <P,Q> : e(P,Q)
    pair_PQ = P.weil_pairing(Q, 3**ea)

    # Allow T = aP + bQ as a linear combination of the basis
    # Via the Weil pairing, we have:
    # e(T, Q) = e(P, Q)^a
    # e(T, P) = e(P, Q)^-b => e(T, -P) = e(P, Q)^b
    pair_a = T.weil_pairing(Q, 3**ea)
    pair_b = T.weil_pairing(-P, 3**ea)

    # Recover a,b using the dlog in Fp2
    a = pair_a.log(pair_PQ)
    b = pair_b.log(pair_PQ)

    return (Mod(b, 3**ea) / a).lift()
