""" secret sharing """

import sys

from ffield import *
from matrix import *
from random import randrange

if sys.version_info[0] < 3 :
  zp = zip;
  mp = map;
else :
  def zp(*x) :
    """Python 2 version of zip"""
    return list(zip(*x));

  def mp(*x) :
    """Python 2 version of map"""
    return list(map(*x));

from ffield import stradix,radstix
from rational import ceil,log,log2

def hexify(r,radix=16) :
  """Given a finite field, make its __str__ output in radix radix """
  n = ceil(log(r.__len__(),radix));
  r.__str__ = lambda self: stradix(self.x,radix,n);

def Vandermonde(xs,k=0) :
  """Given a list of "numbers"
and an optional degree (default: length of list),
return a Vandermonde matrix with rows corresponding to the "numbers"
and columns corresponding to powers from 0 to degree-1"""
  n = len(xs);
  k = k or n;
  return matrix(n,k,[x**i for i in range(k) for x in xs]);

#F = ffield(2,256,1061)
#F = ffield(2,128,135)
F = ffield(2,64,27);
hexify(F);

#GF2_138 = ffield(2,138,365);    # 21 ASCII characters (95 possibilities each)
#GF2_184 = ffield(2,184,349);    # 28 ASCII characters (95 possibilities each)
GF2_230 = ffield(2,230,189);    # 35 ASCII characters (95 possibilities each)

def asciify(x) :
  """Turn int x into a printable ASCII string"""
  a = [];
  while x :
    x,r = divmod(x,95);
    a.append(chr(32+r));
  return ''.join(a[-1::-1]).strip();

GF2_230.__str__ = lambda self: asciify(self.x);

def iicsa(s) :
  """Turn a stripped printable ASCII string into an int"""
  x = 0;
  for c in s.strip() :
    x = 95*x+ord(c)-32;
  return x;

def shares(s,n,k) :
  """Given a secret s in some finite field or other numeric class such as
rational, int, float, or complex (or an up-to-21-character printable ASCII
secret string which is interpreted as a field element of GF_138),
a number of shares n, and the required number of shares k,
return a list of n pairs (sharer,share)
any k of which can recover the secret.
Note that built-in numeric classes might not recover the secret exactly."""
  if isinstance(s,str) :
    s = GF2_230(iicsa(s));
  sharers = mp(s.__class__,range(1,n+1));
  try :
    pn = s.p**s.n;
  except Exception :
    pn = 1;
    while pn <= abs(s) : pn *= 2;
  return zp(sharers,Vandermonde(sharers,k)*([s]+[s.__class__(randrange(pn)) for i in range(k-1)]));

def secret(xs) :
  """Given a list of k (sharer,share) pairs, return the secret"""
  z = zp(*xs);
  return str((Vandermonde(z[0])**-1*z[1])[0]);

def printshares(ss) :
  """Given list of (sharer,share) pairs, print it as a matrix"""
  zss = zp(*ss);
  print(matrix(len(ss),2,zss[0]+zss[1]));

def selectshares(ss,*args) :
  """Given list of (sharer,share) pairs, select specified shares"""
  return [ss[i] for i in args];

def mungeshare(xs,j,t) :
  """Given list of k (sharer,share) pairs, change just element j to give secret t"""
  if isinstance(t,str) :
    t = GF2_230(iicsa(t));
  z = zp(*xs);
  v = Vandermonde(z[0])**-1;
  ds = (t-(v*z[1])[0])/v[0,j];
  return [s if i!=j else (s[0],s[1]+ds) for i,s in enumerate(xs)];
