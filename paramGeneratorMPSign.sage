
# MPSign parameter selection and evaluation script
# Ver. 1.0 
import sys;

#orig_stdout = sys.stdout
#f = open('MPSign_pars_out_a.txt', 'w')
#sys.stdout = f



# NIST cat-1/cat0/cat1/cat2/cat3/cat5 classical gate complexity goals
log2cat_1secClsgt = 79; # AES 64 classical number of gates complexity goal
log2cat0secClsgt = 111; # AES 96 classical number of gates complexity goal
log2cat1secClsgt = 143; # AES 128 classical number of gates complexity goal
log2cat2secClsgt = 175; # AES 160 classical number of gates complexity goal
log2cat3secClsgt = 207; # AES 192 classical number of gates complexity
log2cat5secClsgt = 272; # AES 256 classical number of gates complexity

def maxi(x,y) :
	if (x > y) :
		m = x;
	else :
		m = y;
	return m
																																
# NIST cat-1/cat0/cat1/cat2/cat3/cat5 quantum gate complexity goals for min/med/max MAXDEPTH assumptions 

# min/med/max quantum circuit MAXDEPTH assumptions
#log2MAXDEPTHmax = 96;
#log2MAXDEPTHmed = 64;
log2MAXDEPTHmin = 40;

log2cat_1secmax = maxi(106-log2MAXDEPTHmin, 64/2+21); # AES 64 ("cat -1" max security target in No. of Quant. gates).
log2cat0secmax = maxi(138-log2MAXDEPTHmin, 96/2+21); # AES 96 ("cat 0" max security target in No. of Quant. gates).
log2cat1secmax = maxi(170-log2MAXDEPTHmin, 128/2+21); # AES 128 ("cat 1" max security target in No. of Quant. gates).
log2cat2secmax = maxi(202-log2MAXDEPTHmin, 160/2+21); # AES 160 ("cat 2" max security target in No. of Quant. gates).
log2cat3secmax = maxi(233-log2MAXDEPTHmin, 192/2+21); # AES 192 ("cat 3" max security target in No. of Quant. gates).
log2cat5secmax = maxi(298-log2MAXDEPTHmin, 256/2+21); # AES 256 ("cat 5" max security target in No. of Quant. gates).

def mini(x,y) :
	if (x > y) :
		m = y;
	else :
		m = x;
	return m

# log_2(gate complexity) per G/H/XOF Random oracle call 
#log2TRO = 15;
#log2TQRO = 19;
#DepthQRO = 2^13;
#log2MAXDEPTHminprime = mini(log2MAXDEPTHmin,log2SelQsecgoal)
#Q_d = 2^log2MAXDEPTHminprime/DepthQRO;


#
# *** Part 1: Parameter Selection ***
R = RealField(256); # 256 bit precision reals

# * inputs: initial target values *

# Dimension param targets
targn = 2500;
targd = 1300;
targk = 512;

# error/secret Gaussian distribution s and sd, alpha and alphasd params targets
# note: s = sd * sqrt(2*pi), alpha = s/q, alphasd = sd / q
targsd_sec = 2^(0.5);
targsd_err = 2^(0.5);

# signing sampling acceptance probability (expected no. of sign iterations = 1/targ_pacc)
targ_pacc = R(1/3);

# Selected quantum/classical security parameter Goals
lamQgoal = log2cat1secmax;
lamCgoal = log2cat1secClsgt;

# upper bound on log_2 of number of attack sign queries goal 
logqsgoal = 64;


# * outputs: initial derived params values *

# Gaussian s params
s_sec = R( targsd_sec * (2*pi)^0.5 );
s_err = R( targsd_err * (2*pi)^0.5 );

# logDH(k,kap): returns log_2 of size of challenge space D_H
def logDH(k,kap) :
	logDH = R(log(binomial(k+1,kap)) / log(2))+kap;
	return logDH

# kap = challenge weight derivation to satisy Security cond 1: |D_H| > 2^{lamCgoal}
# after the loop below, logDHval = log |D_H|
kap = 1;
logDHval = logDH(targk,kap);
while  ((logDHval < 2*lamCgoal+log(40)/log(2)) and (kap < targk))  :
	kap = kap + 1;
	logDHval = logDH(targk,kap);


# bound on inf. Norm of secret, uses min. Of Renyi tail-cut bound [BLLSS15] for ~< 1 bit  #sec loss and tail bound #of centered binomial with std dev targsd_sec
secinfbndval = R(min(targsd_sec * float((2*log(2*(targn+targd+targk-1)))^(1/2)), 2*targsd_sec^2));

A1 = R( kap*secinfbndval* ( (1-targ_pacc^(1/(2*(targn+targd-1))))^(-1) - 1 ) - 0.5 );
A1 = ceil(A1);

# bound on inf. Norm of error, uses min. Of Renyi tail-cut bound [BLLSS15] and tail bound #of centered binomial with std dev targsd_sec
errinfbndval = R(min(targsd_sec * float((2*log(2*(targd+targk)))^(1/2)), 2*targsd_sec^2));

A2 = R( kap*errinfbndval* ( (1-targ_pacc^(1/(2*targd)))^(-1) - 1 ) - 0.5 );
A2 = ceil(A2);


# a1, a2 = masking interval half size for z_1, z_2
# to satisfy rejection sampling security condition 0: a1 >= kap*secinfbnd + A1, a2 >= kap*errinfbnd + A2
a1 = kap*secinfbndval + A1; 
a1 = ceil(a1);

a2 = kap*errinfbndval + A2; 
a2 = ceil(a2);

# qmin = modulus
# to satisfy security condition 3: q >= 2^((lam+3)/d) * |D_H|^(2/d) * (4*A1+1)^(1+(n-1)/d) * (4*A2+1)^(1)
qmin = R( 2^((2*lamCgoal+log(40)/log(2))/targd) * 2^(logDH(targk,kap)*(2/targd)) * (4*A1+1)^(1+(targn-1)/targd) * (4*A2+1)^(1) );
qmin = ceil(qmin);
logqmin = R(log(qmin)/log(2));

# compute security condition 2 lower bound dmin on d, where dmin = ( (lamCgoal+3) + logqsgoal ) / log(2*A2+1)
dmin = R( ( (lamCgoal+3) + logqsgoal ) / (log(2*A2+1)/log(2)) );


# etabin = 4;
# targcmp = 0;
# mmargin = 30;


print("*** Input Parameter target values: *** ");

print("Dimension param targets");
print("n"); print(targn);
print("d"); print(targd);
print("k"); print(targk);

print("secret and error standard deviation param targets");
print("sd_sec"); print(targsd_sec); 
print("sd_err"); print(targsd_err); 

print("signing sampling acceptance probability (expected no. of sign itr = 1/targ_pacc)");
print("targ_paccl"); print(targ_pacc); 

print("quantum/classical security parameter goals");
print("lamQgoal"); print(lamQgoal); 
print("lamCgoal"); print(lamCgoal); 

print("max log_2 number of attack sign queries goal");
print("logqsgoal"); print(logqsgoal); 


print("*** Output Parameter values: *** ");

print("Gaussian s params");
print("s_sec"); print(s_sec);
print("s_err"); print(s_err);

print("Challenge params");
print("kap"); print(kap);
print("logDHval"); print(logDHval);

print("rejection sampling params");
print("rejection interval bit lengths");
print("logA1"); print(R(log(A1)/log(2)));
print("logA2"); print(R(log(A2)/log(2)));
print("rejection mask bit lengths");
print("loga1"); print(R(log(a1)/log(2)));
print("loga2"); print(R(log(a2)/log(2)));

print("modulus q bit length");
print("logqmin"); print(logqmin);

print("dmin security lower bound on d");
print("dmin"); print(dmin);

print("size parameters:");
skkbytelen = float(( (targn+targd+targk-1) * (floor(log(targsd_sec)/log(2))+1) + (targd+targk) * (floor(log(targsd_err)/log(2))+1) )/8/1024) ; 
print("sk kbyte len"); print(skkbytelen);

pkkbytelen = float( ( (targd+targk) * (floor(logqmin)+1) + 256 )/8/1024 ); # assume a is generated from a 256 bit seed by hashing
print("pk kbyte len"); print(pkkbytelen);

sigkbytelen = float( ( (targn+targd-1) * (floor(log(A1)/log(2))+1) + targd * (floor(log(A2)/log(2))+1) + kap * log(targk+1)/log(2) )/8/1024 ); 
print("sig kbyte len"); print(sigkbytelen);

print("Computing Parameter Eval...");

# *** Part 2: Lattice Attack Security Evaluation ***

load("estimator.py")

# PLWE distinguishing attack complexity estimates
epsterm1 = 2^(-32);
epsterm2 = 1;
t = 2; # two sample large secret PLWE = one sample HNF PLWE

mmin = targd+targk;
# assume mmax = n and mmid = (n-(d+k))/2

#n = 1024; q = 12289; stddev = sqrt(16/2); alpha = alphaf(sigmaf(stddev), q);

# MAX FAMILY DIMENSION m = n SECURITY ESTIMATES
m1 = targn; # max PLWE dimension
q1 = qmin;
Tmaxm = 0;
alpha1 = sqrt(2*pi)*targsd_sec/q1;
Nr = 2;
print ("n,alpha,q,Nr");
print(m1);
print(R(alpha1));
print(R(q1));
print(Nr);
print("***");
TmaxmAll = estimate_lwe(n=m1, alpha=alpha1, q=q1, secret_distribution=True, m=m1, reduction_cost_model=BKZ.qsieve);
print("***");

Tmaxm = TmaxmAll['usvp']['rop']; 


# MIDDLE FAMILY DIMENSION m= (n+mmin)/2 SECURITY ESTIMATES
#m = (targn+mmin)/2; # MID PLWE dimension
#alpha = R(targsd_err)/R(q); # LWE alpha parameter (in terms of noise standard deviation).

#log2Tepsmidm = logToptloRat;
#log2TepsmidmC = logToptloRatC;


# MIN FAMILY DIMENSION m = mmin SECURITY ESTIMATES
#m = mmin; # min PLWE dimension
#alpha = R(targsd_err)/R(q); # LWE alpha parameter (in terms of noise standard deviation).

#log2Tepsminm = logToptloRat;
#log2TepsminmC = logToptloRatC;


# LATTICE ATTACK RESULT SUMMARY

print("PLWE ATTACK QUANTUM SECURITY SUMMARY:");
log2Qsecgoal = lamQgoal+1;
print("log2Qsecgoal"); print(log2Qsecgoal);
#print("Tminm (min PLWE dim)"); print(Tminm);
#print("Tmidm (med PLWE dim)"); print(Tmidm);
print("log2Tmaxm (max PLWE dim)"); print(R(log(Tmaxm)/log(2)));

#print(TmaxmAll);

#if (log2Tepsminm > log2Qsecgoal)  :
#	print("ALL PLWE Qsec goals OK");
#else :
#	print("Some PLWE Qsec goals FAIL");

#print("PLWE ATTACK CLASSICAL SECURITY SUMMARY:");
#log2Csecgoal = lamCgoal+1;
#print("log2Csecgoal"); print(log2Csecgoal);
#print("Tminm (min PLWE dim)"); TminmC;
#print("Tmidm (med PLWE dim)"); TmidmC;
#print("Tmaxm (max PLWE dim)"); TmaxmC;

#if (log2TepsminmC > log2Csecgoal)  :
#	print("ALL PLWE Csec goals OK");
#else :
#	print("Some PLWE Csec goals FAIL");



#sys.stdout = orig_stdout;
#f.close();



# In[ ]:





# In[ ]:




# In[ ]:



