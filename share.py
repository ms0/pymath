""" secret sharing """

from ffield import *
from matrix import *
from random import randrange

if sys.version_info[0] < 3 :
  zp = zip;
else :
  def zp(*x) :
    """Python 2 version of zip"""
    return list(zip(*x));

def hexify(r) :
  """Given a finite field, make its __str__ output in hex"""
  r.__str__ = lambda self:'%x'%(self.x);

def Vandermonde(xs,k=0) :
  """Given a list of "numbers", and an optional degree (default: length of list),
return a Vandermonde matrix with rows corresponding to the "numbers" and
columns corresponding to powers from 0 to degree-1"""
  n = len(xs);
  k = k or n;
  return matrix(n,k,[x**i for i in range(k) for x in xs]);

#F = ffield(2,256,1061)
F = ffield(2,64,27);
hexify(F);

def shares(s,n,k) :
  """Given a secret s in some finite field [default F=ffield(2,64,27)],
a number of shares n, and the required number of shares k,
return a list of n pairs (sharer,share) any k of which can recover the secret"""
  sharers = map(s.__class__,range(1,n+1));
  return zp(sharers,Vandermonde(sharers,k)*([s]+[s.__class__(randrange(s.p**s.n)) for i in range(k-1)]));

def secret(xs) :
  """Given a list of k (sharer,share) pairs, return the secret"""
  z = zp(*xs);
  return (Vandermonde(z[0])**-1*z[1])[0];

def printshares(ss) :
  """Given list of (sharer,share) pairs, print it as a matrix"""
  zss = zp(*ss);
  print(matrix(len(ss),2,zss[0]+zss[1]));
