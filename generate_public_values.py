from sage.all import randrange

def generate_torsion_points(E, la, ea, lb, eb):
    """
    Compute a torsion basis for both:
        E[la^ea] = <P3, Q3>,
        E[lb^eb] = <P2, Q2>

    Note: unlike the SIDH spec, Alice used the
    3-torsion and bob uses the 2-torsion
    """
    p = E.base().characteristic()
    def get_l_torsion_basis(E, l):
        n = (p+1) // l
        return (n*G for G in E.gens())
    P3, Q3 = get_l_torsion_basis(E, la**ea)
    P2, Q2 = get_l_torsion_basis(E, lb**eb)
    return P3, Q3, P2, Q2

def check_torsion_points(E, la, ea, lb, eb, P3, Q3, P2, Q2):
    """
    Make sure Torsion basis for alice and bob
    are generated correctly
    """
    return all([la**(ea-1)*P3 != E(0),
                lb**(eb-1)*P2 != E(0),
                P3.weil_pairing(Q3, la**ea)**(la**(ea-1)) != 1,
                P2.weil_pairing(Q2, lb**eb)**(lb**(eb-1)) != 1])

def gen_keypair(E, P, Q, P_other, Q_other, l, e):
    """
    Given a torsion basis of alice and bob's subgroups
    generate a keypair (sk, pk)
    """
    p = E.base().characteristic()

    # generate challenge key
    key = randrange(l**e)
    K = P + key*Q

    # Compute the secret isogeny
    phi = E.isogeny(K, algorithm="factored")
    E_new = phi.codomain()
    E_new.set_order((p+1)**2, num_checks=0)

    # Compute image of torsion points
    P_new, Q_new = phi(P_other), phi(Q_other)
    return key, (E_new, P_new, Q_new)
