from __future__ import division

__all__ = ['polynomial']

import sys
if sys.version_info>(3,) :
  NONE = (None,);
  xrange = range;
  iteritems = lambda x: x.items();
  isint = lambda x: isinstance(x,(int));
  REAL = (int,float);
else :
  NONE = (None,sys.maxint);
  iteritems = lambda x: x.iteritems();
  isint = lambda x: isinstance(x,(int,long));
  REAL = (int,long,float);

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

from collections import defaultdict
from matrix import product
from rational import rational

inf = float('inf');

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
  for c in p :
    v = v*x+c;
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
  mapcoeffs, derivative, gcd, xgcd, factor, @staticmethod unfactor"""

  def __init__(self,*p) :
    """Create a polynomial from a sequence of coefficients, constant term last"""
    for i,c in enumerate(p) :
      if c :
        self._p = tuple(c for c in p[i:]);
        return;
    self._p = ();

  def __hash__(self) :
    return hash(self._p);

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

  def __repr__(self) :
    """Return a string representation of the polynomial"""
    return 'polynomial'+str(self._p);

  def __bool__(self) :
    """Return True unless a zero polynomial"""
    return not not self._p;

  __nonzero__ = __bool__

  def __lt__(self,other) :
    """Compare by degree, and if equal, lexicographically by coeff sequence, constant last"""
    if not isinstance(other,self.__class__) :
      raise TypeError();
    return len(self._p) < len(other._p) or len(self._p) == len(other._p) and self._p < other._p;

  def __le__(self,other) :
    """Compare by degree, and if equal, lexicographically by coeff sequence, constant last"""
    if not isinstance(other,self.__class__) :
      raise TypeError();
    return len(self._p) < len(other._p) or len(self._p) == len(other._p) and self._p <= other._p;

  def __eq__(self,other) :
    """Return True iff coeff sequences of self and other compare equal"""
    if not isinstance(other,self.__class__) :
      raise TypeError();
    return self._p == other._p;

  def __ne__(self,other) :
    """Return False iff coeff sequences of self and other compare equal"""
    if not isinstance(other,self.__class__) :
      raise TypeError();
    return self._p != other._p;

  def __ge__(self,other) :
    """Compare by degree, and if equal, lexicographically by coeff sequence, constant last"""
    if not isinstance(other,self.__class__) :
      raise TypeError();
    return len(self._p) > len(other._p) or len(self._p) == len(other._p) and self._p >= other._p;

  def __gt__(self,other) :
    """Compare by degree, and if equal, lexicographically by coeff sequence, constant last"""
    if not isinstance(other,self.__class__) :
      raise TypeError();
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
      other = polynomial(other);
    return polynomial(*nzpolymul(self._p,other._p));

  __rmul__ = __mul__

  def __truediv__(self,other) :
    """Return the quotient self/other, dropping the remainder"""
    if not other : return ZeroDivisionError;
    if not isinstance(other,self.__class__) :
      other = polynomial(other);
    if not self._p : return self;
    return polynomial(*(nzpolydivrem(self._p,other._p)[0]));

  def __rtruediv__(self,other) :
    """Return the quotient other/self"""
    if not self._p : return ZeroDivisionError;
    if not other : return polynomial();
    return polynomial(other)/self;

  __div__ = __truediv__
  __rdiv__ = __rtruediv__
  __floordiv__ = __truediv__
  __rfloordiv__ = __rtruediv__

  def __divmod__(self,other) :
    """Return the quotient and remainder when dividing self by other"""
    if not other : return ZeroDivisionError;
    if not self._p : return self,self;
    if not isinstance(other,self.__class__) :
      other = polynomial(other);
    q,r = nzpolydivrem(self._p,other._p);
    return polynomial(*q),polynomial(*r);

  def __rdivmod__(self,other) :
    """Return the quotient and remainder when dividing other by self"""
    if not self._p : return ZeroDivisionError;
    if not other : return polynomial(),polynomial();
    return divmod(polynomial(other),self);

  def __mod__(self,other) :
    """Return the remainder when dividing self by other"""
    if not other : return ZeroDivisionError;
    if not self._p : return self;
    if not isinstance(other,self.__class__) :
      other = polynomial(other);
    return polynomial(*(nzpolydivrem(self._p,other._p)[1]));

  def __rmod__(self,other) :
    """Return the remainder when dividing other by self"""
    if not self._p : return ZeroDivisionError;
    if not other : return polynomial();
    return polynomial(other)%self;

  def __pow__(f,e) :
    """Return polynomial f raised to nonnegative integer e: f**e"""
    if not (isint(e) and e >= 0) :
      return TypeError('Exponent must be a nonnegative integer');
    if not e :
      if not f : raise ZeroDivisionError;
      return polynomial(1);
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
    c = (p._p[0] if p else q._p[0] if q else None).__class__;
    if c in REAL :
      return p.mapcoeffs(rational).gcd(q.mapcoeffs(rational)).mapcoeffs(float);
    while q :
      p,q = q, p%q;
    return p and p/p._p[0];

  def xgcd(p,q) :
    """Return (g,u,v), where g = gcd of p and q, and g=up+vq"""
    if not isinstance(q,p.__class__) :
      raise TypeError('both args must be polynomials');
    c = (p._p[0] if p else q._p[0] if q else None).__class__;
    if c in REAL : return tuple(
      map(lambda x: x.mapcoeffs(float),
          p.mapcoeffs(rational).xgcd(q.mapcoeffs(rational))));
    u,v,u1,v1 = _one,_zero,_zero,_one;
    while q :
      m = p//q;
      p,u,v,q,u1,v1 = q,u1,v1,p-m*q,u-m*u1,v-m*v1;
    p0 = p._p[0] if p else 1;
    return p/p0,u/p0,v/p0;

  def factor(self,factors=None,e=1) :
    """Return a factorization of polynomial self as a defaultdict(int);
keys are factors, and values are positive integer exponents;
if the leading coefficient is real (i.e., int or float),
the coefficients are converted to rationals before factoring
and the result's coefficients are converted to floats.
Nonconstant factors will be square-free but not necessarily irreducible."""
    if not isinstance(factors,defaultdict) : factors = defaultdict(int);
    if self.degree < 1 :
      if not self or self._p[0]**2 != self._p[0] :
        factors[self] += 1;
        return factors;
    c = self._p[0].__class__;
    if c in REAL :
      for k,v in iteritems(self.mapcoeffs(rational).factor()) :
        factors[k.mapcoeffs(float)] += v;
      return factors;
    if self._p[0]**2 != self._p[0] :
      factors[polynomial(self._p[0])] += e;
      self /= self._p[0];
    d = self.derivative();
    if not d :
      # must be finite field of charactertic p with poly in x**p
      return polynomial(*(x**c.p**(c.n-1) for x in self._p[::c.p])).factor(factors,c.p*e);
    g = self.gcd(d);
    self /= g
    # now self is square-free, but might have factor in common with g
    i = 1;
    while self.degree :
      h = self.gcd(g);
      self /= h;
      g /= h;
      if self.degree : self._factor(factors,i*e);
      i += 1;
      self = h;
    if g.degree :
      return polynomial(*(x**c.p**(c.n-1) for x in g._p[::c.p])).factor(factors,c.p*e);
    else :
      return factors;

  def _factor(self,factors,e) :    # self is square-free and monic
    try :
      c = self._p[0].__class__;
      q = c.p**c.n;
      i = 1;
      s = ();
      while 2*i <= self.degree :
        o = c(1);
        z = c(0);
        g = self.gcd(polynomial(*(o,)+((z,)*(q**i-2))+(-o,z))); # x**q**i - x
        if g.degree :
          factors[g] += e    # actually want g's factors, all of degree i
          self /= g;
        i += 1;
      if self.degree :
        factors[self] += e;     # must be irreducible
    except :
      factors[self] += e;

  def mapcoeffs(self,f) :
    """Apply f to each coefficient and return the resulting polynomial"""
    return polynomial(*map(f,self._p));

  @staticmethod
  def unfactor(factors,p=None) :
    """Take a factorization as produced by factor() and return the product,
multiplied by p if specified"""
    if p == None : p = _one;
    for f,e in iteritems(factors) :
      p *= f**e;
    return p;

_zero = polynomial();
_one = polynomial(1);
