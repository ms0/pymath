from __future__ import division

__all__ = ['polynomial','rationalfunction']

import sys

from itertools import chain, count
from collections import defaultdict
from matrix import product
from rational import rational,xrational
from ffield import isprime, factors, isirreducible, modpow, ffield, primalitytestlimit
from random import randrange,randint

if sys.version_info>(3,) :
  NONE = (None,);
  xrange = range;
  iteritems = lambda x: x.items();
  isint = lambda x: isinstance(x,int);
  INT = set((int,));
  REAL = set((int,float,rational));
else :
  NONE = (None,sys.maxint);
  iteritems = lambda x: x.iteritems();
  isint = lambda x: isinstance(x,(int,long));
  INT = set((int,long));
  REAL = set((int,long,float,rational));

RATIONAL = set((rational,));
COMPLEX = REAL | set((complex,xrational));
XRATIONAL = set((rational,xrational));

try :
  int.bit_length;
  bit_length = lambda n : n.bit_length();
except :
  import math
  def bit_length(n) :
    if n :
      n = abs(n);
      l = int(math.log(n,2));
      while n >> l : l += 1;
      return l;
    return 0;

inf = float('inf');
floatall = lambda x: x.mapcoeffs(float);
complexall = lambda x: x.mapcoeffs(complex);
identity = lambda x: x;

def leastfactor(n) :
  if n <= 1: return 1;
  if n > primalitytestlimit and isprime(n) : return n;
  if not n&1 : return 2;
  for p in count(3,2) :
    if p*p > n : return n;
    if not n%p : return p;

# danger: division converts to floating point (unless we use rational coeffs)

def nzpolymul(f,g) :
  fg = (len(f)+len(g)-1)*[0*f[0]];
  for i in xrange(len(f)) :
    for j in xrange(len(g)) :
      fg[i+j] += f[i]*g[j];
  return fg;

def nzpolypow(b,e) :
  n = (1 << (bit_length(e)-1)) >> 1;
  x = b;
  while n :
    x = nzpolymul(x,x);
    if e&n :
      x = nzpolymul(x,b);
    n >>= 1;
  return x;

def nzpolydivrem(f,g) :
  """Return the quotient and remainder from dividing polynomial f by polynomial g"""
  r = list(f);
  dr = len(r)-1;
  dg = len(g)-1;
  q = [];
  for i in xrange(dr-dg+1) :
    q.append(r[i]/g[0]);
    for j in xrange(dg+1) :
      r[i+j] = (r[i+j]-q[-1]*g[j]);
  while r and not r[0] : r = r[1:];
  return tuple(q),tuple(r);

# evaluate a univariate polynomial (an iterable of coefficients), at a point
def evaluate(p,x) :
  v = 0*x;
  one = x**0;    # to handle matrices properly
  for c in p :
    v = v*x+c*one;
  return v;

class polynomial() :
  """polynomial in one variable
sequence of coefficients ending with constant term; leading zeroes are elided;
a zero polynomial has an empty sequence of coefficients

Instance variables:
  degree: the degree of the polynomial [-inf for a zero polynomial, 0 for a constant]
  
Methods:
  __init__, __hash__, __iter__, __call__, __repr__, __bool__, __nonzero__,
  __lt__, __le__, __eq__, __ne__, __ge__, __gt__, __pos__, __neg__,
  __add__, __radd__, __sub__, __rsub__, __mul__, __rmul__,
  __truediv__, __rtruediv__, __div__, __rdiv__, __floordiv__, __rfloordiv__,
  __divmod__, __mod__, __rmod__, __pow__,
  mapcoeffs, derivative, gcd, xgcd, isirreducible, factor, @staticmethod unfactor"""

  def __init__(self,*p) :
    """Create a polynomial from a sequence of coefficients, constant term last"""
    for i,c in enumerate(p) :
      if c :
        self._p = tuple(c for c in p[i:]);
        return;
    self._p = ();

  def __hash__(self) :
    return hash(self._p if len(self._p) > 1 else self[0]);

  def __getattr__(self,name) :
    if name == 'degree' :
      return len(self._p)-1 if self._p else -inf;
    raise AttributeError('%s has no attribute %s'%(self.__class__.__name__,name));

  def __iter__(self) :
    """Return an iterable of the coefficients starting with the constant term"""
    return reversed(self._p);

  def __getitem__(self,key) :  # get coefficient of x**key
    """Get coefficent indexed by nonnegative integer, or tuple of coeffs by slice.
Coefficients are indexed by the associated exponent, so 0 indicates the constant term;
indices larger than the degree give 0; indices < 0 raise exception;
[::-1] gives a tuple of coeffs with constant term last"""
    if isint(key) :
      if key < 0 : raise IndexError('Negative indices not allowed');
      return self._p[len(self._p)-1-key] if 0 <= key < len(self._p) else 0;
    if isinstance(key,slice) :
      x = [key.start,key.stop,key.step];
      if x[2] == None : x[2] = 1;
      if x[0] == None : x[0] = 0 if x[2] > 0 else len(self._p)-1;
      if x[1] in NONE : x[1] = -1 if x[2] < 0 else len(self._p);
      if x[0] < 0 or x[1] < -1 : raise IndexError('Negative indices not allowed');
      return tuple(self[i] for i in xrange(*x));
    return KeyError('index must be integer or slice');

  def __call__(self,x) :
    """Evaluate the polynomial at x"""
    return evaluate(self._p,x);

  def __str__(self) :
    return str(self[0]) if self.degree < 1 else 'polynomial('+','.join(map(str,self._p))+')'

  def __repr__(self) :
    """Return a string representation of the polynomial"""
    return 'polynomial('+','.join(map(str,self._p))+')';

  def __bool__(self) :
    """Return True unless a zero polynomial"""
    return not not self._p;

  def __len__(self) :
    """Return max(0,self.degree+1)"""
    return len(self._p);

  __nonzero__ = __bool__

  def __lt__(self,other) :
    """Compare by degree, and if equal, lexicographically by coeff sequence, constant last"""
    if not isinstance(other,self.__class__) : other = self.__class__(other);
    return len(self._p) < len(other._p) or len(self._p) == len(other._p) and self._p < other._p;

  def __le__(self,other) :
    """Compare by degree, and if equal, lexicographically by coeff sequence, constant last"""
    if not isinstance(other,self.__class__) : other = self.__class__(other);
    return len(self._p) < len(other._p) or len(self._p) == len(other._p) and self._p <= other._p;

  def __eq__(self,other) :
    """Return True iff coeff sequences of self and other compare equal"""
    if not isinstance(other,self.__class__) : other = self.__class__(other);
    return self._p == other._p;

  def __ne__(self,other) :
    """Return False iff coeff sequences of self and other compare equal"""
    if not isinstance(other,self.__class__) : other = self.__class__(other);
    return self._p != other._p;

  def __ge__(self,other) :
    """Compare by degree, and if equal, lexicographically by coeff sequence, constant last"""
    if not isinstance(other,self.__class__) : other = self.__class__(other);
    return len(self._p) > len(other._p) or len(self._p) == len(other._p) and self._p >= other._p;

  def __gt__(self,other) :
    """Compare by degree, and if equal, lexicographically by coeff sequence, constant last"""
    if not isinstance(other,self.__class__) : other = self.__class__(other);
    return len(self._p) > len(other._p) or len(self._p) == len(other._p) and self._p > other._p;

  def __pos__(self) :
    """Return self"""
    return self;

  def __neg__(self) :
    """Return -self, a poly with all coeffs negated"""
    return polynomial(*tuple(-cs for cs in self._p));

  def __add__(self,other) :
    """Return the sum self+other"""
    if not isinstance(other,self.__class__) :
      if isinstance(other,rationalfunction) : return other+self;
      other = polynomial(other);
    if len(self._p) < len(other._p) : self,other = other,self;
    d = len(self._p) - len(other._p);
    return polynomial(*tuple(cs if i<0 else cs+other._p[i] for i,cs in enumerate(self._p,-d)));

  __radd__ = __add__;

  def __sub__(self,other) :
    """Return the difference self-other"""
    return self+-other;

  def __rsub__(self,other) :
    """Return the difference other-self"""
    return -self+other;

  def __mul__(self,other) :      
    """Return the product self*other"""
    if not self or not other : return polynomial();
    if not isinstance(other,self.__class__) :
      if isinstance(other,rationalfunction) : return other*self;
      other = polynomial(other);
    return polynomial(*nzpolymul(self._p,other._p));

  __rmul__ = __mul__

  def __floordiv__(self,other) :
    """Return the quotient self//other, dropping the remainder"""
    if not other : raise ZeroDivisionError;
    if not isinstance(other,self.__class__) :
      if isinstance(other,rationalfunction) :
        if other._b != 1 :
          return other.__rfloordiv__(self);
        other = other._a;
      else :
        other = polynomial(other);
    if not self._p : return self;
    return polynomial(*(nzpolydivrem(self._p,other._p)[0]));

  def __rfloordiv__(self,other) :
    """Return the quotient other//self"""
    if not self._p : raise ZeroDivisionError;
    if not other : return polynomial();
    return polynomial(other)//self;

  def __div__(self,other) :
    """Return the quotient self/other as a polynomial or rationalfunction"""
    if other == 1 : return self;
    if isinstance(other,rationalfunction) :
      if other._b != 1 :
        return other.__rdiv__(self)
      other = other._a;
    if isinstance(other,polynomial) and other.degree <= 0 :
      other = other[0] if other else 0;
    if not isinstance(other,RATFUN) :
      if other :
        return self.mapcoeffs(lambda x:x/other);
      raise ZeroDivisionError;
    q = rationalfunction(self,other);
    return q if q._b != 1 else q._a;

  def __rdiv__(self,other) :
    """Return the quotient other/self"""
    return self.__class__(other)/self;

  __truediv__ = __div__
  __rtruediv__ = __rdiv__

  def __divmod__(self,other) :
    """Return the quotient and remainder when dividing self by other"""
    if not other : raise ZeroDivisionError;
    if not self._p : return self,self;
    if not isinstance(other,self.__class__) :
      if isinstance(other,rationalfunction) :
        if other._b != 1 :
          return other.__rdiv__(self),polynomial();
        other = other._a;
      else :
        other = polynomial(other);
    q,r = nzpolydivrem(self._p,other._p);
    return polynomial(*q),polynomial(*r);

  def __rdivmod__(self,other) :
    """Return the quotient and remainder when dividing other by self"""
    if not self._p : raise ZeroDivisionError;
    if not other : return polynomial(),polynomial();
    return divmod(polynomial(other),self);

  def __mod__(self,other) :
    """Return the remainder when dividing self by other"""
    if not other : raise ZeroDivisionError;
    if not self._p : return self;
    if not isinstance(other,self.__class__) :
      if isinstance(other,rationalfunction) :
        if other._b == 1 :
          other = other._a;
        return polynomial();
      else :
        other = polynomial(other);
    return polynomial(*(nzpolydivrem(self._p,other._p)[1]));

  def __rmod__(self,other) :
    """Return the remainder when dividing other by self"""
    if not self._p : raise ZeroDivisionError;
    if not other : return polynomial();
    return polynomial(other)%self;

  def __pow__(f,e) :
    """Return polynomial f raised to integer e: f**e"""
    if not isint(e) :
      raise TypeError('Exponent must be an integer');
    if f.degree <= 0 :
      return polynomial(f[0]**e);
    if e <= 0:
      if e :
        return rationalfunction(f[f.degree].__class__(1),polynomial(*nzpolypow(f._p,-e)));
      return polynomial(f[f.degree].__class__(1));
    return polynomial(*nzpolypow(f._p,e));

  def derivative(self,k=1) :    # kth derivative
    """Return the kth derivative of self"""
    if not (isint(k) and k >= 0) :
      raise TypeError('kth derivative only defined for k nonegative integer');
    d = len(self._p);
    return polynomial(*tuple(product(xrange(d-i,d-i-k,-1),c)
                             for i,c in enumerate(self._p[:d-k],1)));
  def gcd(p,q) :
    """Return the greatest common divisor of polynomials p and q"""
    if not isinstance(q,p.__class__) :
      raise TypeError('both args must be polynomials');
    types = set();
    for x in chain(p,q) :
      types.add(x.__class__);
    if types <= REAL and not types <= RATIONAL :
      p = p.mapcoeffs(rational);
      q = q.mapcoeffs(rational);
      mapping = floatall;
    elif types <= COMPLEX and not types <= XRATIONAL :
      p = p.mapcoeffs(xrational);
      q = q.mapcoeffs(xrational);
      mapping = complexall;
    else :
      mapping = identity;
    while q :
      p,q = q, p%q;
    return mapping(p and p/p._p[0]);

  def xgcd(p,q) :
    """Return (g,u,v), where g = gcd of p and q, and g=up+vq"""
    if not isinstance(q,p.__class__) :
      raise TypeError('both args must be polynomials');
    types = set();
    for x in chain(p,q) :
      types.add(x.__class__);
    if set() < types <= REAL and not types <= RATIONAL :
      p = p.mapcoeffs(rational);
      q = q.mapcoeffs(rational);
      mapping = floatall;
    elif types <= COMPLEX and not types <= XRATIONAL :
      p = p.mapcoeffs(xrational);
      q = q.mapcoeffs(xrational);
      mapping = complexall;
    else :
      mapping = identity;
    u,v,u1,v1 = _one,_zero,_zero,_one;
    while q :
      m = p//q;
      p,u,v,q,u1,v1 = q,u1,v1,p-m*q,u-m*u1,v-m*v1;
    p0 = p._p[0] if p else 1;
    return mapping(p/p0),mapping(u/p0),mapping(v/p0);

  def isirreducible(p,q=0) :
    """Return True iff p is irreducible over a field;
if q is specified, it is the size of the field;
if q is not specified, the field is inferred from p's coefficients"""
    if q :
      r = factors(q) ;
      if len(r) != 1 :
        raise ValueError('q must be a prime power')
    d = p.degree;
    if d <= 1 :
      return True;
    types = set();
    for x in p :
      types.add(x.__class__);
    if types <= INT and q > 0:
      r = r[0];
      if p._p[0] != 1 :
        i = modpow(p._p[0],r-2,r);    # make monic
        p = p.mapcoeffs(lambda x: x*i%r);
        if d != p.degree :
          raise ValueError('leading coefficient is 0 mod %d'%(r));
      return isirreducible(p._p[1:],q);
    if len(types) == 1 and tuple(types)[0].__class__ == ffield :
      p0 = p._p[0];
      if int(p0) != 1 :
        p = p.mapcoeffs(lambda x: x/p0);    # make monic
      q = q or p0.p**p0.n;
      for c in p :
        if (q-1)%(c.order or 1) :
          raise ValueError('coefficients not all elements of GF(%d)'%(q));
      x = polynomial(p._p[0],p._p[0]*0);    # Rabin test...
      s = factors(d)+(1,);
      k = len(s);
      for i in xrange(k) :
        e = q**(d//s[i]);
        n = 1 << (bit_length(e)-1);
        y = x;
        n >>= 1;
        while n :
          y = y*y%p;
          if e&n :
            y = x*y%p;
          n >>= 1;
        if s[i] > 1 :
          if p.gcd(y-x).degree != 0 : return False;
        else :
          return not (y-x)%p;
    raise TypeError('implemented only for finite fields');

  def factor(self,facdict=None,e=1) :
    """Return a factorization of polynomial self as a defaultdict(int);
keys are factors, and values are positive integer exponents;
if the leading coefficient is real (i.e., int or float),
the coefficients are converted to rationals before factoring
and the result's coefficients are converted to floats.
Nonconstant factors will be square-free but not necessarily irreducible."""
    if not isinstance(facdict,defaultdict) : facdict = defaultdict(int);
    if self.degree < 1 :
      if not self or self._p[0]**2 != self._p[0] :
        facdict[self] += e;
      return facdict;
    types = set();
    for x in self :
      types.add(x.__class__);
    if set() < types <= REAL and not types <= RATIONAL :
      for k,v in iteritems(self.mapcoeffs(rational).factor()) :
        facdict[k.mapcoeffs(float)] += v;
      return facdict;
    elif types <= COMPLEX and not types <= XRATIONAL :
      for k,v in iteritems(self.mapcoeffs(xrational).factor()) :
        facdict[k.mapcoeffs(complex)] += v;
      return facdict;
    if self._p[0]**2 != self._p[0] :
      facdict[polynomial(self._p[0])] += e;
      self /= self._p[0];
    g = self.gcd(self.derivative());
    self //= g
    # now self is square-free, but might have factor in common with g
    i = 1;
    while self.degree :
      h = self.gcd(g);
      self //= h;
      g //= h;
      if self.degree : self._factor(facdict,i*e);
      i += 1;
      self = h;
    if g.degree :    # finite field...
      c = g._p[0];
      p = c.p;    # characteristic
      px = p**(c.n-1);    # exponent for mapping a**p -> a for a in GF(p**n)
      return polynomial(*(x**px for x in g._p[::p])).factor(facdict,p*e);
    else :
      return facdict;

  def _factor(self,facdict,e) :    # self is square-free and monic
    try :
      c = self._p[0].__class__;
      q = c.p**c.n;
      i = 1;
      s = ();
      while 2*i <= self.degree :
        z = c(0);
        o = c(1);
        h = b = polynomial(o,z);    # compute x**q**i % self ...
        x = q**i;
        m = (1<<(bit_length(x)-1)) >> 1;
        while m :
          h = h*h%self;
          if x&m :
            h = polynomial(*h._p+(z,))%self;
          m >>= 1;
        g = self.gcd(h-b);
        n = g.degree;
        if n :
          # Cantor-Zassenhaus algorithm...
          f = set((g,));
          self //= g;
          r = n//i;    # number of degree i irreducible factors
          if r > 1 :
            x = (q**i-1)//leastfactor(q**i-1);
            while len(f) < r :
              h = b = polynomial(o,
                *(c(randrange(q)) for j in range(i)))
              m = (1<<(bit_length(x)-1)) >> 1;
              while m :
                h = h*h%g;
                if x&m :
                  h = h*b%g;
                m >>= 1;
              h -= c(1);
              h = h.mapcoeffs(lambda x:x/h._p[0]);
              for u in tuple(f) :
                if u.degree > i :
                  for w in (h,b) :
                    v = u.gcd(w);
                    if 0 < v.degree < u.degree :
                      f.remove(u);
                      f.add(v);
                      f.add(u//v);
                      break;
          for u in f :
            facdict[u] += e;
        i += 1;
      if self.degree :
        facdict[self] += e;     # must be irreducible
    except :
      facdict[self] += e;

  def mapcoeffs(self,f) :
    """Apply f to each coefficient and return the resulting polynomial"""
    return polynomial(*map(f,self._p));

  @staticmethod
  def unfactor(facdict,p=None) :
    """Take a factorization as produced by factor() and return the product,
multiplied by p if specified"""
    if p == None : p = _one;
    for f,e in iteritems(facdict) :
      p *= f**e;
    return p;

class rationalfunction() :
  def __init__(self,a,b=1) :
    if not b : raise ZeroDivisionError;
    a = rationalize(a);
    b = rationalize(b);
    g = a.gcd(b)*b[b.degree];    # make denominator monic
    self._a = a//g;
    self._b = b//g;

  def __str__(self) :
    return '%s/%s'%(self._a,self._b) if self._b != 1 else str(self._a);

  def __repr__(self) :
    return 'rationalfunction(%s,%s)'%(self._a,self._b);

  def __getattr__(self,name) :
    if name == 'degree' :
      return self._a.degree - self._b.degree;
    if name in ('a','numerator') :
      return self._a;
    if name in ('b','denominator') :
      return self._b;
    raise AttributeError('%s has no attribute %s'%(self.__class__.__name__,name));

  def __hash__(self) :
    return hash(self._a if self._b == 1 else (self._a,self._b));

  def __pos__(self) :
    return self;

  def __neg__(self) :
    return rationalfunction(-self._a,self._b);

  def __call__(self,x) :
    return self._a(x)/self._b(x);

  def __eq__(self,other) :
    if not isinstance(other,rationalfunction) :
      other = rationalfunction(other);
    return self._a*other._b == self._b*other._a;

  def __ne__(self,other) :
    if not isinstance(other,rationalfunction) :
      other = rationalfunction(other);
    return self._a*other._b != self._b*other._a;

  def __le__(self,other) :
    if not isinstance(other,rationalfunction) :
      other = rationalfunction(other);
    return self._a*other._b <= self._b*other._a;

  def __lt__(self,other) :
    if not isinstance(other,rationalfunction) :
      other = rationalfunction(other);
    return self._a*other._b < self._b*other._a;

  def __ge__(self,other) :
    if not isinstance(other,rationalfunction) :
      other = rationalfunction(other);
    return self._a*other._b >= self._b*other._a;

  def __gt__(self,other) :
    if not isinstance(other,rationalfunction) :
      other = rationalfunction(other);
    return self._a*other._b > self._b*other._a;

  def __add__(self,other) :
    if not isinstance(other,rationalfunction) :
      other = rationalfunction(other);      
    return rationalfunction(self._a*other._b+self._b*other._a,self._b*other._b);

  __radd__ = __add__

  def __sub__(self,other) :
    if not isinstance(other,rationalfunction) :
      other = rationalfunction(other);
    return rationalfunction(self._a*other._b-self._b*other._a,self._b*other._b);

  def __rsub__(self,other) :
    if not isinstance(other,rationalfunction) :
      other = rationalfunction(other);
    return rationalfunction(other._a*self._b-other._b*self._a,self._b*other._b);

  def __mul__(self,other) :
    if not isinstance(other,rationalfunction) :
      other = rationalfunction(other);      
    return rationalfunction(self._a*other._a,self._b*other._b);

  __rmul__ = __mul__

  def __div__(self,other) :
    if not isinstance(other,rationalfunction) :
      other = rationalfunction(other);
    return rationalfunction(self._a*other._b,self._b*other._a);

  def __rdiv__(self,other) :
    if not isinstance(other,rationalfunction) :
      other = rationalfunction(other);
    return rationalfunction(self._b*other._a,self._a*other._b);

  __truediv__ = __floordiv__ = __div__
  __rtruediv__ = __rfloordiv__ = __rdiv__

  def __pow__(self,other) :
    if not isint(other) :
      raise TypeError('exponent must be integer');
    if other < 0 :
      if not self : raise ZeroDivisionError;
      return rationalfunction(self._b**-other,self.__a**-other);
    return rationalfunction(self.a**other,self.b**other);
  
def rationalize(p) :
  if isinstance(p,polynomial) :
    types = set();
    for x in p :
      types.add(x.__class__);
    if set() < types <= REAL and not types <= RATIONAL :
      return p.mapcoeffs(rational);
    elif types <= COMPLEX and not types <= XRATIONAL :
      return p.mapcoeffs(xrational);
  elif p.__class__ in REAL :
    return polynomial(rational(p));
  elif p.__class__ in COMPLEX :
    return polynomial(xrational(p));
  return p;

_zero = polynomial();
_one = polynomial(1);

RATFUN = (polynomial,rationalfunction);
