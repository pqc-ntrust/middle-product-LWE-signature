#implementation of the attack in the MPSign paper
import numpy as np
import time
from sage.modules.free_module_integer import IntegerLattice
#parameters are those from Section 4
k=6
q=next_prime(2^30)
n=1459
d=1111
beta=14

print "k is: ",k,",q is: ",q,",n is: ",n,",d is: ",d,",beta is",beta
def generate_polynomial(degree,lower_bound_coeff,upper_bound_coeff):
	poly=0
	list_of_coefficients=[]
	for i in range(degree+1):
		coeff=randint(lower_bound_coeff,upper_bound_coeff)
		poly=poly+x^i*coeff
		list_of_coefficients.append(coeff)
	return poly,list_of_coefficients
A=[]
S=[]	
def generate_public_key(nr_samples,modulus):
	R.<x>=PolynomialRing(Integers(modulus))
	t_poly=0
	for i in range(k):
		a_poly,a_coeff=generate_polynomial(n-1,0,q-1)
		A.append(a_coeff)
		s_poly,s_coeff=generate_polynomial(d-1,-beta,beta)
		S.append(s_coeff)
		t_poly=t_poly+a_poly*s_poly	
	t_coeff=t_poly.coefficients(sparse=false)
	return A, S, t_coeff


#here I generate the public key Amatrix and t_coeff and the secret key Smatrix (where I store the coefficients of the corresponding polynomials)
A,S,t_coeff=generate_public_key(k,q)
Amatrix=MatrixSpace(Integers(q),k,n)(A)
Smatrix=MatrixSpace(Integers(q),k,d)(S)

#goodness test to reject bad AMatrix and continue only on good matrix.

bad=1;
time0=time.time()
sum = 0;

# homogenous knapsack basis lattice
ainv = inverse_mod(ZZ(Amatrix[k-1][0]),q);
sbar = mod(ainv * sum,q);
Bhom=matrix.identity(k-1)
Chom=matrix(1,k-1)
Dhom=matrix(1,1,[q])
Ehom=matrix(k-1,1,[mod((-1)*ainv*Amatrix[i][0],q) for i in range(k-1)])
#F=matrix(k-1,1)
#G=matrix(1,1,[0])
latticehom=block_matrix(ZZ,[[Bhom,Ehom],[Chom,Dhom]],subdivide=false)
#lattice[k+1,k]=mod(lattice[k+1,k],q)
#here I apply LLL and hope to recover the r coefficients of the shortest hom. lat. vec.
short_vectorhom=IntegerLattice(latticehom).LLL()[0]
for i in range(k):
	if (short_vectorhom[i]*short_vectorhom[i] > (2*beta)*(2*beta)):
		bad = 0;
time1=time.time()

if (bad==0):
	

  #now I try to attack the public key a_1,..a_k,t and find s_1,...,s_6

  #I build my initial solution matrix as the zero matrix and I will continously update it
  solution=np.zeros((k,d),int)

  #here I find the r'th coefficients of the s_i's and store the solution I find in the matrix solution on column r
  time0=time.time()
  for r in range(d):
	partial_sum=0
	for i in range(k):
		for j in range(r):
			partial_sum=partial_sum+Amatrix[i][r-j]*solution[i][j]
	sum=t_coeff[r]-ZZ(partial_sum)
	
	# primal embedding lattice approach
	# compute *some* large solution bar
	# namely sbar_0=...=sbar_{k-2} = 0, sbar_{k-1} = a_{k-1}^{-1} * sum mod q
	ainv = inverse_mod(ZZ(Amatrix[k-1][0]),q);
	sbar = mod(ainv * sum,q);
	c = isqrt(k)*beta;


	B=matrix.identity(k-1)
	C=matrix(ZZ,2,k-1)
	D=matrix(ZZ,2,1,[q,sbar])
	E=matrix(ZZ,k-1,1,[mod((-1)*ainv*Amatrix[i][0],q) for i in range(k-1)])
	F=matrix(ZZ,k-1,1)
	G=matrix(ZZ,2,1,[0,c])
	lattice=block_matrix(ZZ,[[B,E,F],[C,D,G]],subdivide=false)
	#lattice[k+1,k]=mod(lattice[k+1,k],q)

 	#here I apply LLL and hope to recover the r coefficients of the s_i's
	short_vector=IntegerLattice(lattice).LLL()[0]
	for i in range(k):
		solution[i][r]=short_vector[i]
	# negate the solution if the last coefficient of short_vector is -1
	if (short_vector[k] < 0): 
		for i in range(k):
			solution[i][r]=(-1)*short_vector[i]	
  time1=time.time()


  #here I check the solution 
  numberGoodColumns=0
  for j in range(d):
	ok=0
	for i in range(k):
		if (mod(Smatrix[i][j],q)!=mod(solution[i][j],q)):
			ok=1
	if (ok==0):
		numberGoodColumns=numberGoodColumns+1
  print "I recovered",numberGoodColumns,"good columns out of",d, "in ",time1-time0,"seconds"


	

	
	

