from __future__ import division

""" BCH error correcting code generation """

from conversions import gcd
from numbers import primepower
from ffield import ffield
from poly import polynomial
from random import randrange
from matrix import bmatrix

def lcm(p,q) :
  """Return least common multiple of polynomials p and q"""
  return p*q//p.gcd(q);

def bch(q,n,d,c=1) :
  """Generate BCH code, return generator polynomial
  symbols are in GF(q)
  n symbols in codeword
  d is the required minimum Hamming distance between codewords
  c is least of consecutive exponents of primitive root used for computing result
  NOTE: computations and results are in GF(q**m); so if q is not prime,
   converting results back to GF(q) will not be unique."""
  try :
    p,k = primepower(q);
  except Exception :
    raise ValueError('q must be a prime power');
  if not 2 <= d <= n : raise ValueError('must have 2 <= d <= n');
  if gcd(n,p) != 1 : raise ValueError('n and q must be coprime');
  m = 1;    # calculate m, the order of q mod n ...
  t = q;
  while t%n != 1 :
    m += 1;
    t = t*q%n;
  qm = q**m;    # 1 mod n (so n|(q**m-1))
  F = ffield(qm);
  while True :
    a = F(randrange(1,qm));
    if not a.order%n : break;
  a = a**(a.order//n);    # primitive nth root in F = GF(q**m)
  g = polynomial(F(1));
  for e in range(c,c+d-1) :
    g = lcm(g,(a**e).minpolynomial(k));
  return g;    # note m can be retrieved from g[0] attributes

# n is the number of symbols in codeword
# d is the minimum Hamming distance between codewords
# g.degree is the number of checksum symbols
# so n - g.degree is the number of data symbols

# how do we generate the codewords?
# data symbols become the coeffs of a polynomial p.
# codewords are coeffs of polynomial p*g
# but to get systematic encoding,
# use s = p*x**t - p*x**t%g

################################################################################
# given generator poly and tuple of data symbols, return codeword tuple
def encode(g,d) :
  """Given generator polynomial g and tuple d of data symbols,
return codeword tuple"""
  s = polynomial(*(d+(0,)*g.degree));
  s = s - s%g;
  return s[len(d)+g.degree-1::-1];    # codeword tuple, each element in GF(q**m)

# get generator matrix for size n, d distance binary BCH code
def bchmatrix(n,d) :
  """Return generator matrix for binary BCH code with
n-bit codewords and Hamming distance >= d"""
  g = bch(2,n,d);
  b = n - g.degree;
  return bmatrix(n,b,sum(
    (list(map(int,encode(g,tuple(map(int,format(1<<i,'0%db'%(b)))))))
     for i in reversed(range(b))),
    [])).T;

# given generator matrix, return parity check matrix
def pcheckmatrix(G) :
  """Given generator matrix G, return parity check matrix"""
  c = type(G);
  k,n = G.dims;    # number of data bits and size of codeword
  H = c(n,n-k);
  H[:k,:] = G[:,k:]
  H[k:,:] = c.Identity(n-k);
  return H;
