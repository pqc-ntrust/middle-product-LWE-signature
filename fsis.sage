# This is a POC code for f-SIS signature scheme
import time
from hashlib import sha256
from sage.stats.distributions.discrete_gaussian_integer import DiscreteGaussianDistributionIntegerSampler



# sample parameters from page 11 of eprint: 2016-796
n = 1459
k = 6
q = 1073741827      # next prime of 2^30
s = 1535
d1 = 1111
d2 = 1285
c = 36
sigma = 54509336    # \approx 2^25.7

# input polynomials a and b in the form of a list
# (with lead pad 0s), return a*b, padded to length
# len(a) + len(b) - 1
def poly_mul(a, b):
    # the polynomial ring
    P.<x> = PolynomialRing(ZZ)

    # multiplication
    c = P(a) * P(b) % q

    # form the output as a list in case of leading 0s
    return [c[i] for i in range(len(a) + len(b) - 1)]


# hash a polynomial and a message into a trinary polynomial
# f whose degree
# is bounded by d2-d1+1 and l1 norm bounded by c
def hash_c(poly, msg):
    degree = d2-d1+1
    f = [0 for _ in range(degree)]

    hash_ctr = 0
    # hash_input = poly | msg | 0
    hash_input = bytes(poly) + bytes(msg) + bytes(hash_ctr)
    hasher = sha256(hash_input)
    hash_ctr += 1
    hash_output = list(hasher.digest())

    # keep setting the indices for f until we get kappa 1s
    index_ctr = 0
    while index_ctr < c:
        if len(hash_output) == 0:
            # we have consumed the whole hash output
            # get a new set of outputs by update the
            # hash with the counter
            hasher.update(bytes(hash_ctr))
            hash_ctr += 1
            hash_output = list(hasher.digest())
        # get 16 bits from hash, mod it by degree to generate an index
        # FIXME: this will not be uniform for degree that is not power of 2
        b1 = ord(hash_output.pop())
        b2 = ord(hash_output.pop())
        index = ((b1 << 8) + b2) % degree

        if f[index] == 0:
            # FIXME: f[index] should be either 1 or -1 with equal prob
            f[index] = 1
            index_ctr += 1
    return f


# contineous Normal distribution over R^m,
# certer: v
# variance: sigma
# output probability at x
def rho(v, sigma, x):
    m = x.degree();
    norm = (x-v).norm(2)
    const = RR((1/sqrt(2*pi)/sigma)^m)
    return RR(const * e^(-norm^2/2/sigma^2))

# rejection sampling, a subroutine of signing algorithm
# the sigma and d2 are implicit inputs from global
# siclist is the list of s_i * c, pre-computed during signing
def rejection_sampling (zlist, siclist, c):
    z = []
    for e in zlist:
        z += e
    # print vector(z).degree()

    s = []
    for e in siclist:
        s += e

    zero_vec = vector([0 for _ in range(k*d2)]);
    z = vector(z)
    s = vector(s)

    # we need to compute compute D_{sigma}(z) / D_{s,sigma}(z)
    # that is
    #   \rho_{0, sigma}^m(z) / \rho_{sigma}^m(\ZZ)
    #   ---------------------------------------
    #   \rho_{s, sigma}^m(z) / \rho_{sigma}^m(\ZZ)
    # which is indeed
    #   \rho_{0, sigma}^m(z)
    #   --------------------
    #   \rho_{s, sigma}^m(z)
    res = rho(zero_vec, sigma, z)/ rho(s, sigma, z) / 3

    # now sample a random t in [0,1]
    # if t < res, ouput "accept"
    t = RR.random_element(0,1)
    # print t, RR(res)
    if t < res:
        return True
    else:
        return False



def keygen():
    alist = []
    slist = []
    t = [0 for _ in range(n+d1-1)]
    for i in range(k):
        # a_i is a random poly in R^{<n}
        ai = [ZZ.random_element(0,q) for _ in range(n)]
        alist.append(ai)
        # s_i is a random poly in R_s^{<d1}
        si = [ZZ.random_element(-s, s+1) for _ in range(d1)]
        slist.append(si)
        # t = \sum ai * si
        tmp = poly_mul(ai, si)
        t = [(t[j] + tmp[j])%q for j in range(n+d1-1)]

    # covert t into a list and lead pad with 0s if needed
    t = [t[i]%q for i in range(n+d1-1)]

    return ((alist, t), slist)


def sign(msg, pk, sk):
    D = DiscreteGaussianDistributionIntegerSampler(sigma)
    accept = False
    counter = 0
    while accept == False:
        ylist = []
        # hash_input = \sum^k a_i y_i which is part of the input to hash
        hash_input = [0 for _ in range(n+d2-1)]
        for i in range(k):
            # y_i is a poly in R^{d2} following discrete Gaussian
            yi = [D() for _ in range(d2)]
            ylist.append(yi)
            tmp2 = poly_mul(pk[0][i],yi)
            hash_input = [(hash_input[j] + tmp2[j])%q for j in range(n+d2-1)]

        # c = hash(tmp | msg)
        c = hash_c(hash_input, msg)

        # z_i = s_ic + yi
        zlist = []
        # use this list to store si * c that is to be used during
        # rejection sampling
        siclist = []
        for i in range(k):
            tmp = poly_mul(sk[i], c)
            zi = [(tmp[j] + ylist[i][j])%q for j in range(d2)]
            zlist.append(zi)
            siclist.append(tmp)

        accept = rejection_sampling (zlist, siclist, c)
        counter += 1

    return (zlist, c, counter)


def verify(pk, sig, msg):
    # FIXME: check the norm bounds
    # check each z_i's degree is less than d2
    # and infinity norm is less than 5*sigma
    five_sigma = 5*sigma
    for e in sig[0]:
        if len(e) > d2:
            return False, "False: incorrect length"
        # center mod e, and then the norm
        for i in range(d2):
            e[i] %= q;
            if (e[i]) > q/2:
                e[i] -= q
            if abs(e[i]) >= five_sigma:
                return False,  "False: incorrect norm"

    # compute c' = hash(hash_input | msg), where
    # hash_input = \sum a_i z_i - tc, and checks if c = c'

    hash_input = [0 for _ in range(n+d2-1)]
    # tmp_prime = \sum a_i z_i
    for i in range(k):
        tmp2 = poly_mul(pk[0][i], sig[0][i])
        hash_input = [(hash_input[j]+tmp2[j])%q for j in range(n+d2-1)]
    # tmp_prime = \sum a_i z_i - tc
    tmp2 = poly_mul(pk[1], sig[1])
    hash_input = [(hash_input[j]-tmp2[j])%q for j in range(n+d2-1)]

    # compute c' and checks if it equals to c
    c_prime = hash_c(hash_input, msg)
    return sig[1] == c_prime, ""


# get the min, med, max, average of the list
def get_data(list):
    R = RealField(20)
    list.sort()
    v = vector(list)
    v = v.change_ring(R)
    length = v.length()
    sum = 0
    for e in v:
        sum +=e
    ave = sum/length
    med = (length - 1)//2
    return v[0], v[med], v[length-1], R(ave)



iter_num = 1001

keygen_time_list = []
num_RS_list = []
# keygen_cycle_list = []
sign_time_list = []
verify_time_list = []


for i in range(iter_num):
    # keygen_cycle_one_run = process_time()
    keygen_time_one_run = time.clock()
    (pk, sk) = keygen()
    keygen_time_one_run = time.clock() - keygen_time_one_run
    # keygen_cycle_one_run = process_time() - keygen_cycle_one_run
    keygen_time_list.append(keygen_time_one_run)
    # keygen_cycle_list.append(keygen_cycle_one_run)

    sign_time_one_run = time.clock()
    sig = sign("message to sign"+ZZ(i).str(), pk, sk)
    sign_time_one_run =  time.clock() - sign_time_one_run
    sign_time_list.append(sign_time_one_run)

    verify_time_one_run = time.clock()
    ver = verify(pk, sig, "message to sign"+ZZ(i).str())
    verify_time_one_run = time.clock() - verify_time_one_run
    verify_time_list.append(verify_time_one_run)

    num_RS_list.append(sig[2])

tmp = get_data(keygen_time_list)
print "key gen --- min:", tmp[0], "med:", tmp[1], "max:", tmp[2], "ave:", tmp[3]
tmp = get_data(sign_time_list)
print "sign    --- min:", tmp[0], "med:", tmp[1], "max:", tmp[2], "ave:", tmp[3]
tmp = get_data(num_RS_list)
print "# RS    --- min:", tmp[0], "med:", tmp[1], "max:", tmp[2], "ave:", tmp[3]
tmp = get_data(verify_time_list)
print "verify  --- min:", tmp[0], "med:", tmp[1], "max:", tmp[2], "ave:", tmp[3]
