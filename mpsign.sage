# this is a POC code for MPSign scheme

from hashlib import sha256
from sage.stats.distributions.discrete_gaussian_integer import DiscreteGaussianDistributionIntegerSampler

# this section defines public parameters.
n = 2500
d = 1300
k = 512
kappa = 53                          # hamming weight of the challenge polynomial c
q = 190510370427772390705463296     # modulus, ~2^87.3
alpha_prime = 1.41421356237310                # std dev of discrete gaussian for s
alpha_double_prime = 1.41421356237310         # std dev of discrete gaussian for e
a_prime = 1466299                   # infty norm bound for y1
a_double_prime = 501831             # infty norm boudn for y2
# bound_sec = 212
# bound_sec = 343
A_prime = 1466086                   # rejection sampling parameter for z1
A_double_prime = 501618             # rejection sampling parameter for z2

# We try to avoid using polynomial rings as much as possible.
# The objects we are dealing with will be fixed length lists,
# so that we can catch bugs where polys have leading 0s.
# Using list instead of polynomials will also enforce the
# length/degree of the polynomials we are going to add matches.


# input polynomials a and b, parameters d
# return a*b mod x^{k+d} rounded by x^k
def mp_mul(a, b, d):
    # the polynomial ring
    P.<x> = PolynomialRing(ZZ)

    # get parameter k which should be an even integer
    da = len(a)
    db = len(b)
    k = (da+db-1-d)
    assert k%2==0, "k is odd"
    k = k//2

    # middle product
    c = P(a) * P(b) % P(x^(k+d))
    c = c // P(x^k)
    # form the output as a list in case of leading 0s
    return [c[i] for i in range(d)]


# hash a polynomial and a message into a binay polynomial
# f whose degree
# is bounded by k and hamming weight bounded by kappa
def hash_c(poly, msg):
    f = [0 for _ in range(k+1)]

    hash_ctr = 0
    # hash_input = poly | msg | 0
    hash_input = bytes(poly) + bytes(msg) + bytes(hash_ctr)
    hasher = sha256(hash_input)
    hash_ctr += 1
    hash_output = list(hasher.digest())

    # keep setting the indices for f until we get kappa 1s
    index_ctr = 0
    while index_ctr < kappa:
        if len(hash_output) == 0:
            # we have consumed the whole hash output
            # get a new set of outputs by update the
            # hash with the counter
            hasher.update(bytes(hash_ctr))
            hash_ctr += 1
            hash_output = list(hasher.digest())
        # get 16 bits from hash, mod it by k to generate an index
        # this will not be uniform for k that is not power of 2
        b1 = ord(hash_output.pop())
        b2 = ord(hash_output.pop())
        index = ((b1 << 8) + b2) % k

        if f[index] == 0:
            f[index] = 1
            index_ctr += 1
    return f

def center_lift(poly):
    res = []
    for e in poly:
        t = e % q
        if t > q/2:
            t = t-q
        res.append(t)
    return res

# generate a set of keys using global public parameters
def keygen():

    # a is a uniform polynomial
    a = [ZZ.random_element(0,q) for _ in range (n)]

    # s is sampled from Gaussian
    D = DiscreteGaussianDistributionIntegerSampler(alpha_prime)
    s = [D() for _ in range (n+d+k-1)]

    # e is also sampled from Gaussian, with a different sigma
    D = DiscreteGaussianDistributionIntegerSampler(alpha_double_prime)
    e = [D() for _ in range (d+k)]

    # b = a mp s + e
    tmp = mp_mul(a, s, d+k)
    assert len(tmp) == len(e), "length do not match"
    b = [(tmp[i] + e[i]) % q for i in range(len(tmp))]
    b = center_lift(b)
    return ((a,b), (s,e,a))

# sign a message with the secret key, and public parameters
def sign(sk, msg):

    accept = False
    counter = 0
    while accept == False:

        # y1, a random poly with norm bound a_prime
        y1 = [ZZ.random_element(-a_prime, a_prime+1) for _ in range (n+d-1)]

        # y2, a random poly with norm bound a_double_prime
        y2 = [ZZ.random_element(-a_double_prime, a_double_prime+1) for _ in range (d)]

        # c = hash(a mp y1 + y2 | msg)
        tmp = mp_mul(sk[2], y1, d)
        assert len(tmp) == len(y2), "length do not match"
        tmp = [(tmp[i] + y2[i]) %q for i in range(len(tmp))]
        tmp = center_lift(tmp)
        c = hash_c(tmp, msg)

        # z1 = c mp s + y1
        tmp = mp_mul(c, sk[0], n+d-1)
        tmp = center_lift(tmp)
        assert len(tmp) == len(y1), "length do not match"
        z1 = [(tmp[i] + y1[i]) %q for i in range(len(tmp))]
        z1 = center_lift(z1)

        # z2 = c mp e + y2
        tmp = mp_mul(c, sk[1], d)
        tmp = center_lift(tmp)
        assert len(tmp) == len(y2), "length do not match"
        z2 = [(tmp[i] + y2[i]) %q for i in range(len(tmp))]
        z2 = center_lift(z2)

        # we need to have concrete parameters for rejection sampling to work
        P.<x> = PolynomialRing(ZZ)
        accept = (P(z1).norm(infinity) <= A_prime) and (P(z2).norm(infinity) <= A_double_prime)

        counter += 1

#        print "repeated", counter, "times"
#    print "finished within", counter, "times"
    return (z1, z2, c, counter)


# Verification takes in a public key, a messag and
# a signature, returns true if verification passes
def verify(pk, msg, sig):
    P.<x> = PolynomialRing(ZZ)
    if (P(sig[0]).norm(infinity) <= A_prime) and (P(sig[1]).norm(infinity) <= A_prime):

        # tmp = tmp1 + z2 - tmp2
        # tmp1 = a mp z1
        # tmp2 = c mp b
        tmp1 = mp_mul(pk[0], sig[0], d)
        tmp1 = center_lift(tmp1)
        tmp2 = mp_mul(sig[2], pk[1], d)
        tmp2 = center_lift(tmp2)
        assert len(tmp1) == len(tmp2), "length do not match"
        assert len(tmp1) == len(sig[1]), "length do not match"
        tmp = [(tmp1[i] + sig[1][i] - tmp2[i]) % q for i in range(len(tmp1))]
        tmp = center_lift(tmp)
        # c = hash(a mp z1 + z2 - c mp b | msg)
        c_prime = hash_c(tmp, msg)

        # signature is valid if c == c_prime
        return c_prime == sig[2]
    else:
        return False



# generate a set of keys
(pk,sk) = keygen()
# signs a message
sig = sign(sk, "msg to sign")
# verifies the signature
ver = verify(pk, "msg to sign", sig)
assert ver, "verification failed"

total = 0
for i in range(10):
    (pk,sk) = keygen()
    sig = sign(sk, "msg to sign" + ZZ(i).str())
    ver = verify(pk, "msg to sign" + ZZ(i).str(), sig)
    assert ver, "verification failed"
    total += sig[3]

# expecting a repeatation rate of 3
print total/1000




keygen_time = time.clock()
for i in range(100):
    _ = keygen()
keygen_time = time.clock() - keygen_time
print keygen_time

total = 0
sig_list = []
pk_list = []
sign_time = time.clock()
for i in range(100):
    (pk, sk) = keygen()
    sig = sign(sk, "message to sign"+ZZ(i).str())
    sig_list.append(sig)
    pk_list.append(pk)
sign_time = time.clock() - sign_time

print sign_time

ver_time = time.clock()
for i in range(100):
    ver = verify(pk_list[i],  "message to sign"+ZZ(i).str(), sig_list[i])
#    print ver
ver_time = time.clock() -  ver_time


for i in range(100):
    total += sig_list[i][3]
print ver_time, RR(total/100)
