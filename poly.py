from __future__ import division

__all__ = ['polynomial','rationalfunction']

import sys

from itertools import chain, count, combinations
from collections import defaultdict
from . matrix import product, bmatrix
from . rational import rational, xrational, inf, realize, sqrt
from . conversions import bit_length, xrange, isint, iteritems, isffield, lmap
from . numfuns import factor, factors, leastfactor, ffactors, primepower, modpow, isirreducible, isprimitive, gcda, lcma, divisors, primes
from random import randrange,randint

def select(a,b) :
  """Given iterable object a and bitmap b (a nonnegative int),
  return those elements of a corresponding to 1s in b, as a generator"""
  for i,x in enumerate(a) :
    if not b : return;
    if b&1 :
      yield x;
    b >>= 1;

if sys.version_info>(3,) :
  INT = set((int,));
  REAL = set((int,float,rational));
else :
  INT = set((int,long));
  REAL = set((int,long,float,rational));

RATIONAL = set((rational,));
COMPLEX = REAL | set((complex,xrational));
XRATIONAL = set((rational,xrational));

int_float = lambda x: x if isint(x) else x.a if abs(x.b)==1 else float(x);

def nzpolymul(f,g) :
  fg = (len(f)+len(g)-1)*[0*f[0]];
  for i in xrange(len(f)) :
    for j in xrange(len(g)) :
      fg[i+j] += f[i]*g[j];
  return fg;

def nzpolypow(b,e,m=None) :
  n = (1 << (bit_length(e)-1)) >> 1;
  if m :
    types = set();
    for c in chain(b,m) :
      types.add(type(c));
    if types <= COMPLEX and not types <= XRATIONAL :
      b = lmap(rational,b);
      m = lmap(rational,m);
      t = realize;
    else :
      t = None;
    x = b = nzpolymod(b,m);
    while n :
      x = nzpolymod(nzpolymul(x,x),m);
      if e&n :
        x = nzpolymod(nzpolymul(x,b),m);
      n >>= 1;
      if t :
        x = tuple(map(t,x));
  else :
    x = b;
    while n :
      x = nzpolymul(x,x);
      if e&n :
        x = nzpolymul(x,b);
      n >>= 1;
  return x;

def nzpolymod(f,g,t=False) :
  """Divide polynomial f by polynomial g to return remainder;
     if t, and coeffs are all numbers, rationalize args and realize result"""
  dr = len(f)-1;
  dg = len(g)-1;
  if dr < dg :
    return f;
  if t :
    types = set();
    for c in chain(f,g) :
      types.add(type(c));
    if types <= COMPLEX and not types <= XRATIONAL :
      f = lmap(rational,f);
      g = lmap(rational,g);
      t = realize;
    else :
      t = None;
  r = f if t else list(f);
  x = 1/g[0];
  for i in xrange(dr+1-dg) :
    if r[i] :
      q = r[i]*x;
      for j in xrange(1,dg+1) :
        r[i+j] = (r[i+j]-q*g[j]);
  for i in xrange(dr+1-dg,dr+1) :
    if r[i] : break;
  else :
    return ();
  return tuple(map(t,r[i:]) if t else r[i:]);

def nzpolydivrem(f,g,t=False) :
  """Divide polynomial f by polynomial g; return quotient and remainder;
     if t, and coeffs are all numbers, rationalize args and realize results"""
  dr = len(f)-1;
  dg = len(g)-1;
  if dr < dg :
    return (),f;
  q = [];
  if t :
    types = set();
    for c in chain(f,g) :
      types.add(type(c));
    if types <= COMPLEX and not types <= XRATIONAL :
      f = lmap(rational,f);
      g = lmap(rational,g);
      t = realize;
    else :
      t = None;
  r = f if t else list(f);
  x = 1/g[0];
  for i in xrange(dr+1-dg) :
    q.append(r[i]*x);
    if q[-1] :
      for j in xrange(1,dg+1) :
        r[i+j] = (r[i+j]-q[-1]*g[j]);
  for i in xrange(dr+1-dg,dr+1) :
    if r[i] : break;
  else :
    return tuple(map(t,q) if t else q),();
  return (tuple(map(t,q) if t else q),
          tuple(map(t,r[i:]) if t else r[i:]));

# evaluate a univariate polynomial (an iterable of coefficients), at a point
def evaluate(p,x) :
  v = 0*x;
  one = x**0;    # to handle matrices properly
  for c in p :
    v = v*x+c*one;
  return v;

class polynomial(object) :
  """polynomial in one variable
sequence of coefficients ending with constant term; leading zeroes are elided;
a zero polynomial has an empty sequence of coefficients

Instance variables:
  degree: the degree of the polynomial [-inf for a zero polynomial, 0 for a constant]
  numerator (aka a): the polynomial itself
  denominator (aka b): the constant polynomial 1 
  
Methods:
  __init__, __hash__, __repr__, __str__,
  __bool__, __nonzero__, __len__, __iter__, __call__,
  __lt__, __le__, __eq__, __ne__, __ge__, __gt__, __pos__, __neg__,
  __add__, __radd__, __sub__, __rsub__, __mul__, __rmul__,
  __truediv__, __rtruediv__, __div__, __rdiv__, __floordiv__, __rfloordiv__,
  __divmod__, __mod__, __rmod__, __pow__, __lshift__, __rshift__,
  mapcoeffs, realize, derivative, gcd, xgcd,
  isirreducible, isprimitive, factor, @staticmethod unfactor"""

  def __init__(self,*p) :
    """Create a polynomial from a sequence of coefficients, constant term last"""
    for i,c in enumerate(p) :
      if c :
        self._p = p[i:];
        return;
    self._p = ();

  def __hash__(self) :
    return hash(self._p if len(self._p) > 1 else len(self._p) and self._p[0]);

  @property
  def degree(self) :
    """degree of polynomial"""
    return len(self._p)-1 if self._p else -inf;

  @property
  def numerator(self) :
    """numerator of rational function"""
    return self;

  @property
  def denominator(self) :
    """denominator of rational function"""
    return _one;

  @property
  def a(self) :
    """numerator of rational function"""
    return self;

  @property
  def b(self) :
    """denominator of rational function"""
    return _one;

  def __iter__(self) :
    """Return an iterable of the coefficients starting with the constant term"""
    return reversed(self._p);

  def __getitem__(self,key) :  # get coefficient(s)
    """Get coefficent indexed by integer, or tuple of coeffs by slice.
Coefficients are indexed by the associated exponent, 0 gives the constant term;
exponents larger than the degree give 0; indices < 0 add degree+1;
slices are treated normally, but can be extended with 0s for exponent > degree;
Note that [::-1] gives a tuple of coeffs with constant term last"""
    l = len(self._p);
    if isint(key) :
      if key < 0 :
        key += l;
        if key < 0 : raise IndexError('index out of range');

      return self._p[l-1-key] if 0 <= key < l else 0;
    if isinstance(key,slice) :
      start,stop,step = key.start,key.stop,key.step;
      if step is None :
        step = 1;
      if start is None :
        start = l-1 if step < 0 else 0;
      elif start < 0 :
        start = start+l if step < 0 else 0;
      if stop is None :
        stop = -1 if step < 0 else l;
      elif stop < 0 :
        stop += l;
        if step < 0 and stop < 0 : stop = -1;
      v = self._p[::-1][key];
      l = (stop-start)//step - len(v);
      return v if l <= 0 else (0,)*l+v if step < 0 else v+(0,)*l;
    raise KeyError('index must be integer or slice');

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
    if not isinstance(other,type(self)) : other = type(self)(other);
    return len(self._p) < len(other._p) or len(self._p) == len(other._p) and self._p < other._p;

  def __le__(self,other) :
    """Compare by degree, and if equal, lexicographically by coeff sequence, constant last"""
    if not isinstance(other,type(self)) : other = type(self)(other);
    return len(self._p) < len(other._p) or len(self._p) == len(other._p) and self._p <= other._p;

  def __eq__(self,other) :
    """Return True iff coeff sequences of self and other compare equal"""
    if not isinstance(other,type(self)) : other = type(self)(other);
    return self._p == other._p;

  def __ne__(self,other) :
    """Return False iff coeff sequences of self and other compare equal"""
    if not isinstance(other,type(self)) : other = type(self)(other);
    return self._p != other._p;

  def __ge__(self,other) :
    """Compare by degree, and if equal, lexicographically by coeff sequence, constant last"""
    if not isinstance(other,type(self)) : other = type(self)(other);
    return len(self._p) > len(other._p) or len(self._p) == len(other._p) and self._p >= other._p;

  def __gt__(self,other) :
    """Compare by degree, and if equal, lexicographically by coeff sequence, constant last"""
    if not isinstance(other,type(self)) : other = type(self)(other);
    return len(self._p) > len(other._p) or len(self._p) == len(other._p) and self._p > other._p;

  def __pos__(self) :
    """Return self"""
    return self;

  def __neg__(self) :
    """Return -self, a poly with all coeffs negated"""
    return type(self)(*tuple(-cs for cs in self._p));

  def __add__(self,other) :
    """Return the sum self+other"""
    if not isinstance(other,type(self)) :
      if isinstance(other,rationalfunction) : return other+self;
      other = type(self)(other);
    if len(self._p) < len(other._p) : self,other = other,self;
    d = len(self._p) - len(other._p);
    return type(self)(*tuple(cs if i<0 else cs+other._p[i] for i,cs in enumerate(self._p,-d)));

  __radd__ = __add__;

  def __sub__(self,other) :
    """Return the difference self-other"""
    return self+-other;

  def __rsub__(self,other) :
    """Return the difference other-self"""
    return -self+other;

  def __mul__(self,other) :      
    """Return the product self*other"""
    if not self or not other : return _zero;
    if not isinstance(other,type(self)) :
      if isinstance(other,rationalfunction) : return other*self;
      other = type(self)(other);
    return type(self)(*nzpolymul(self._p,other._p));

  __rmul__ = __mul__

  def __floordiv__(self,other) :
    """Return the quotient self//other, dropping the remainder"""
    if not other : raise ZeroDivisionError;
    if not isinstance(other,type(self)) :
      if isinstance(other,rationalfunction) :
        if other._b != 1 :
          return other.__rfloordiv__(self);
        other = other._a;
      else :
        other = type(self)(other);
    if not self._p : return self;
    return type(self)(*(nzpolydivrem(self._p,other._p,True)[0]));

  def __rfloordiv__(self,other) :
    """Return the quotient other//self"""
    if not self._p : raise ZeroDivisionError;
    if not other : return _zero;
    return type(self)(other)//self;

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
    return rationalfunction(self,other);

  def __rdiv__(self,other) :
    """Return the quotient other/self"""
    return type(self)(other)/self;

  __truediv__ = __div__
  __rtruediv__ = __rdiv__

  def __divmod__(self,other) :
    """Return the quotient and remainder when dividing self by other"""
    if not other : raise ZeroDivisionError;
    if not self._p : return self,self;
    if not isinstance(other,type(self)) :
      if isinstance(other,rationalfunction) :
        if other._b != 1 :
          return other.__rdiv__(self),_zero;
        other = other._a;
      else :
        other = type(self)(other);
    q,r = nzpolydivrem(self._p,other._p,True);
    return type(self)(*q),type(self)(*r);

  def __rdivmod__(self,other) :
    """Return the quotient and remainder when dividing other by self"""
    if not self._p : raise ZeroDivisionError;
    if not other : return _zero,_zero;
    return divmod(type(self)(other),self);

  def __mod__(self,other) :
    """Return the remainder when dividing self by other"""
    if not other : raise ZeroDivisionError;
    if not self._p : return self;
    if not isinstance(other,type(self)) :
      if isinstance(other,rationalfunction) :
        if other._b == 1 :
          other = other._a;
        return _zero;
      else :
        other = type(self)(other);
    return type(self)(*(nzpolymod(self._p,other._p,True)));

  def __rmod__(self,other) :
    """Return the remainder when dividing other by self"""
    if not self._p : raise ZeroDivisionError;
    if not other : return _zero;
    return type(self)(other)%self;

  def __pow__(self,e,m=None) :
    """Return self raised to integer e: self**e; if m, mod polynomial m"""
    if not isint(e) :
      raise TypeError('exponent must be an integer');
    if not (m is None or isinstance(m,polynomial) and m.degree > 0) :
      raise TypeError('modulus must be polynomial of degree > 0')
    if self.degree <= 0 :
      return type(self)(self[0]**e);
    if e <= 0:
      if e :
        if m :
          raise ValueError('2nd arg cannot be negative when 3rd arg specified');
        return rationalfunction(type(self[self.degree])(1),type(self)(*nzpolypow(self._p,-e)));
      return type(self)(type(self[self.degree])(1));
    return type(self)(*nzpolypow(self._p,e,m and m._p));

  def __lshift__(self,k) :
    """Return self * x**k"""
    if not isint(k) :
      raise TypeError('k must be an integer');
    d = self.degree;
    if d < 0 or not k :
      return self;
    p = type(self)();
    p._p = self._p;
    if k > 0 :
      p._p += (type(self._p[0])(0),)*k;
    else :
      for i in xrange(d,d+k-1,-1) :
        if p._p[i] : break;
      p._p = p._p[0:i+1];
      k += d-i;
      if k < 0 :
        return rationalfunction(p,_x.mapcoeffs(type(self._p[0]))**-k);
    return p;

  def __rshift__(self,k) :
    """Return self * x**-k"""
    return self.__lshift__(-k);

  def derivative(self,k=1) :    # kth derivative
    """Return the kth derivative of self"""
    if not (isint(k) and k >= 0) :
      raise TypeError('kth derivative only defined for k nonegative integer');
    d = len(self._p);
    return type(self)(*tuple(product(xrange(d-i,d-i-k,-1),c)
                             for i,c in enumerate(self._p[:d-k],1)));
  def gcd(p,q) :
    """Return the greatest common divisor of polynomials p and q"""
    if not isinstance(q,type(p)) :
      raise TypeError('both args must be polynomials');
    types = set();
    for x in chain(p,q) :
      types.add(type(x));
    if types <= COMPLEX and not types <= XRATIONAL :
      p = p.mapcoeffs(rational);
      q = q.mapcoeffs(rational);
      t = realize;
    else :
      t = None;
    while q :
      p,q = q, p%q;
    return p and (p/p._p[0]).mapcoeffs(t);

  def xgcd(p,q) :
    """Return (g,u,v), where g = gcd of p and q, and g=up+vq"""
    if not isinstance(q,type(p)) :
      raise TypeError('both args must be polynomials');
    types = set();
    for x in chain(p,q) :
      types.add(type(x));
    if types <= COMPLEX and not types <= XRATIONAL :
      p = p.mapcoeffs(rational);
      q = q.mapcoeffs(rational);
      t = realize;
    else :
      t = None;
    u,v,u1,v1 = _one,_zero,_zero,_one;
    while q :
      m,r = divmod(p,q);
      p,u,v,q,u1,v1 = q,u1,v1,r,u-m*u1,v-m*v1;
    p0 = p._p[0] if p else 1;
    return (p/p0).mapcoeffs(t),(u/p0).mapcoeffs(t),(v/p0).mapcoeffs(t);

  def isirreducible(self,q=0) :
    """Return True iff self is irreducible over a field;
if q is specified, it is the size of the field;
if q is not specified, the field is inferred from self's coefficients"""
    if q :
      r = primepower(q);
      if not r :
        raise ValueError('q must be a prime power')
    d = self.degree;
    if d <= 1 :
      return d==1;
    p0 = self._p[0];
    types = set();
    for x in self :
      types.add(type(x));
    if types <= INT and q > 0:
      r = r[0];
      if p0 != 1 :
        i = modpow(p0,r-2,r);    # make monic
        self = self.mapcoeffs(lambda x: x*i%r);
        if d != self.degree :
          raise ValueError('leading coefficient is 0 mod %d'%(r));
      return isirreducible(self._p[1:],q);
    F = type(p0);
    if len(types) == 1 and isffield(F) :
      if p0 != 1 :
        self = self.mapcoeffs(lambda x: x/p0);    # make monic
      if q :
        for c in self :
          if (q-1)%(c.order or 1) :
            raise ValueError('coefficients not all elements of GF(%d)'%(q));
      else :
        q = p0.q;
      x = type(self)(F(1),F(0));    # Rabin test...
      for s in chain(factors(d),(1,)) :
        e = q**(d//s);
        n = 1 << (bit_length(e)-1);
        y = x;
        n >>= 1;
        while n :
          y = y*y%self;
          if e&n :
            y = x*y%self;
          n >>= 1;
        if s > 1 :
          if self.gcd(y-x).degree != 0 : return False;
        else :
          return not (y-x)%self;
    if types <= COMPLEX and complex in types :
      return False;    # only linear polys are irreducible over C
    if types <= REAL and not float in types :
      if not self[0] : return False;    # multiple of x
      m = lcma(map(lambda x:x.denominator,self._p));
      d = gcda(map(lambda x:x.numerator,self._p));
      poly = self = self.mapcoeffs(lambda x:int(m*x/d));
      if self.gcd(self.derivative()).degree > 0 :
        return False;
      for p in primes(self.twicemaxfactorheight+1) :
        p0 = poly._p[0];
        if p0 != 1 :    # make monic
          i = modpow(p0,p-2,p);
          poly = self.mapcoeffs(lambda x: x*i%p);
        if isirreducible(poly._p[1:],p) :
          return True;
        from . ffield import ffield
        F = ffield(p);
        facs = poly.mapcoeffs(F).factor();    # map to GF(p) and factor
        if sum(facs.values()) > len(facs) :   # not square free
          continue;
        for c in xrange(1,(len(facs)>>1)+1) :
          for facc in combinations(facs,c) :
            fac = product(facc);
            for d in divisors(self._p[0]) :
              g = (d*fac).mapcoeffs(lambda x:x.x-p if p>>1 < x.x else x.x);
              if not self._p[-1]%g._p[-1] and not self%g :
                return False;
        return True;
    raise TypeError('not implemented for these coefficient types');

  def isprimitive(self,q=0) :
    """Return True iff self (assumed irreducible) is primitive over a field;
if q is specified, it is the size of the field;
if q is not specified, the field is inferred from self's coefficients"""
    if q :
      r = primepower(q);
      if not r :
        raise ValueError('q must be a prime power')
      p = r[0];
    n = self.degree;
    if n < 1 : raise ValueError("self can't be constant");
    p0 = self._p[0];
    types = set();
    for x in self :
      types.add(type(x));
    if types <= INT and q > 0:
      if p0 != 1 :
        i = modpow(p0,p-2,p);    # make monic
        self = self.mapcoeffs(lambda x: x*i%p);
        if n != self.degree :
          raise ValueError('leading coefficient is 0 mod %d'%(r));
      return p==q and isprimitive(self._p[1:],p);
    F = type(p0);
    if len(types) == 1 and isffield(tuple(types)[0]) :
      if int(p0) != 1 :
        self = self.mapcoeffs(lambda x: x/p0);    # make monic
      if q :
        for c in self :
          if (q-1)%(c.order or 1) :
            raise ValueError('coefficients not all elements of GF(%d)'%(q));
      else :
        q = F.q;
      if q == F.p :
        return isprimitive(self.mapcoeffs(int)._p[1:],q);
      if not self._p[-1] or n == 1 and not (p0+self._p[1]) : return False; # wx or x-1
      o = q**n-1;
      x = _x.mapcoeffs(F);
      one = _one.mapcoeffs(F);
      for f in ffactors(o) :
        if pow(x,o//f,self) == one : return False;
      return True;
    raise TypeError('implemented only for finite fields');

  def factor(self,facdict=None,e=1) :
    """Return a factorization of polynomial self as a defaultdict(int);
keys are factors, and values are positive integer exponents.
If the coefficients are all real (i.e., int or float),
the coefficients are converted to rationals before factoring
and the result's coefficients are converted to ints if integers else floats;
nonconstant factors will be square-free and irreducible over the rationals.
If some coefficients are complex (i.e., xrational or complex),
factors will be square-free but not necessarily irreducible."""
    if not isinstance(facdict,defaultdict) : facdict = defaultdict(int);
    if self.degree < 1 :
      if not self or self._p[0]**2 != self._p[0] :
        facdict[self] += e;
      return facdict;
    types = set();
    for x in self :
      types.add(type(x));
    if set() < types <= REAL and not types <= RATIONAL :
      if types <= INT :
        for k,v in iteritems(self.mapcoeffs(rational).factor()) :
          facdict[k.mapcoeffs(int_float)] += v;
      else :
        f = 1;
        for k,v in iteritems(self.mapcoeffs(rational).factor()) :
          if not k.degree :
            f *= k._p[0]**v;
          elif k.degree > 0 :
            c = k._p[0];
            if c != 1 :
              f *= c**v;
              k /= c;
            facdict[k.mapcoeffs(int_float)] += v;
        if f != 1 :
          facdict[type(self)(int_float(f))] += 1;
      return facdict;
    elif types <= COMPLEX and not types <= XRATIONAL :
      for k,v in iteritems(self.mapcoeffs(xrational).factor()) :
        facdict[k.mapcoeffs(complex)] += v;
      return facdict;
    if self._p[0]**2 != self._p[0] :
      facdict[type(self)(self._p[0])] += e;
      self /= self._p[0];    # make monic
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
      return type(self)(*(x**px for x in g._p[::p])).factor(facdict,p*e);
    else :
      return facdict;

  def _factor(self,facdict,e) :    # self is square-free and monic
    try :
      c = type(self._p[0]);
      q = c.q;
      i = 1;
      s = ();
      while 2*i <= self.degree :
        z = c(0);
        o = c(1);
        h = b = type(self)(o,z);    # compute x**q**i % self ...
        x = q**i;
        m = (1<<(bit_length(x)-1)) >> 1;
        while m :
          h = h*h%self;
          if x&m :
            h = type(self)(*h._p+(z,))%self;
          m >>= 1;
        g = self.gcd(h-b);
        n = g.degree;
        if n :
          # Cantor-Zassenhaus algorithm...
          f = set((g,));
          self //= g;
          r = n//i;    # number of degree i irreducible factors
          if r > 1 :
            if leastfactor(q**i-1,7) > 7 :
              saved = (c,q,z,o)
              q **= 2
              c = c.dfield;
              z = c(0);
              o = c(1);
              g = g.mapcoeffs(c);
              f = set((g,));
            else :
              saved = ();
            x = (q**i-1)//leastfactor(q**i-1);
            while len(f) < r :
              h = b = type(self)(o,
                *(c(randrange(q)) for j in xrange(i)))
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
            if saved :
              c,q,z,o = saved;
              f = map(lambda x:x.mapcoeffs(c),f);
          for u in f :
            facdict[u] += e;
        i += 1;
      if self.degree :
        facdict[self] += e;     # must be irreducible
    except AttributeError :
      if not self._p[-1] :    # self(0) == 0
        facdict[type(self)(self._p[0],self._p[-1])] += e;    # add x as factor
        self = type(self)(*self._p[:-1]);    # divide by x
      if all(isinstance(x,rational) for x in self._p) :    # Q[x] factorization
        m = lcma(map(lambda x:x.denominator,self._p));
        if m != 1 :
          facdict[type(self)(rational(1,m))] += e;
          self = self.mapcoeffs(lambda x:m*x);
        m = 1;    # combine constant factors
        i = [];
        for f,k in facdict.items() :
          if f.degree == 0 :
            i.append(f);
            m *= f._p[0]**k;
        for f in i : del facdict[f];
        if m != 1 : facdict[type(self)(m)] += 1;
        from . ffield import ffield
        if self.degree > 1 :
          if self._p[0] == 1 and self._p[-1] == -1 and not any(self._p[1:-1]) :
            # special case x^n-1
            for d in divisors(self.degree) :
              facdict[self.cyclotomic(d)] += e;
            return;
          for p in primes(self.twicemaxfactorheight+1) :
            F = ffield(p);
            poly = self.mapcoeffs(F);    # map to GF(p)
            poly /= poly[-1];    # make monic
            facs = poly.factor();
            if sum(facs.values()) > len(facs) :    # not square free
              continue;
            c = 1;    # number of factors to combine
            t = set();   # combinations already tried and failed
            v = set();   # combinations to avoid
            while self.degree > 1 and c <= len(facs)>>1 :
              for facc in combinations(facs,c) :
                # facc = set(facc);  # to make order-independent
                if facc in v :
                  continue;
                fac = product(facc);
                for d in divisors(int(self._p[0])) :
                  g = (d*fac).mapcoeffs(lambda x:x.x-p if p>>1 < x.x else x.x);
                  if not self._p[-1]%g._p[-1] and not self%g :
                    facdict[g] += e;
                    self //= g;
                    for fac in facc :
                      del facs[fac];
                    v |= t;
                    t.clear();
                    break;
                else :
                  t.add(facc);
                  continue;
                break;
              else :
                c += 1;
                t.clear();
                v.clear();
            break;    # GF(p) factorization successfully uplifted
      if self != 1 :
        facdict[self] += e;
  
  # Q[x] factoring algorithm:
  # First, extract lcm of coefficient denominators,
  #  and factor resulting Z[x] polynomial ...
  # Given a Z[x] polynomial of degree > 1 with nonzero constant term and with
  #  integer coefficients whose gcd is 1,
  # for each prime p > max abs coefficient * exp(degree) :
  #   mapcoeffs to ffield(p) and divide by leading coefficient to make monic
  #   factor resutling GF(p) polynomial
  #   if not square free, continue to next prime
  #   set c = 1 (c is the number of factors to combine into a trial factor)
  #   while self.degree > 1 and 2c <= number of factors :
  #     for each combination of c factors :
  #       trial factor is product of those c factors
  #       for each (positive) divisor d of high order coefficient of self :
  #         multiply coeffs by d
  #         map coeffs back to SIGNED integers, getting polynomial g
  #         if constant term of g is divisor of constant term of self and
  #           if self % g is 0, append that factor,
  #             self //= g, delete the c factors, break
  #          the other one is irreducible as well and we're done)
  #       else (if not factor g), continue with other combinations
  #     else (if no combinations of c factors work), c += 1
  # NOTE: we may need to try multiple primes if factorization not square free
  # NOTE: we need to try combinations of GF(p) factors to get factors
  #  irreducible over Q[x] but not over any GF(p), e.g., x^4+1.

  def mapcoeffs(self,f) :
    """Apply f to each coefficient and return the resulting polynomial"""
    return type(self)(*map(f,self._p)) if f else self;

  def realize(self) :
    """Apply realize to each coefficient and return the resulting polynomial"""
    return type(self)(*map(realize,self._p));

  @property
  def twicemaxfactorheight(self) :
    """Return twice max possible height of any irreducible factor of Z[x] poly
    using K.Mahler's version of Gelfond formula for any factor's max height"""
    return int((max(map(abs,self))*sqrt(self.degree+1))<<self.degree);

  @staticmethod
  def unfactor(facdict,p=None) :
    """Take a factorization as produced by factor() and return the product,
multiplied by p if specified"""
    if p == None : p = _one;
    for f,e in iteritems(facdict) :
      p *= f**e;
    return p;

  @staticmethod
  def xnm1(n,o=1) :
    """Return polynomial ox^n-o; coefficients all type(o)"""
    z = o-o;    # zero of same type as o
    return polynomial(*(z if 0<i<n else -o if i else o for i in range(n+1)));

  @staticmethod
  def cyclotomic(n) :
    """Return nth cyclotomic polynomial"""
    if not n : return _one;    # optimization required n==0 special case
    xnm1 = polynomial.xnm1;
    # f = tuple(factors(n));   # optimization replaces this with ...
    fe = tuple(factor(n));          # make n square free ...
    f = tuple(f[0] for f in fe);    #  tuple(factors(n))
    p = product(f);                 #  product of prime factors (new n)
    m,n = n//p, p;                  #  multiplier, new n
    p = xnm1(n);               # vanilla computation of cyclotomic(n)
    for b in range((1<<len(f))-1,0,-1) :    # order matters!
      s = tuple(select(f,b));
      d = product(s);    # divisor d with mu(d) != 0
      if len(s)&1 :
        p //= xnm1(n//d);    # mu(d) == -1
      else :
        p *= xnm1(n//d);     # mu(d) == 1
    if m > 1 :   # finalize optimization: replace x with x^m
      p = polynomial(*(0 if i%m else p._p[i//m] for i in range(m*p.degree+1)));
    return p;

class rationalfunction(object) :
  """rational function (ratio of polynomials) in one variable

Instance variables:
  degree: degree of numerator minus degree of denominator
  numerator (aka a): the polynomial numerator
  denominator (aka b): the polynomial denominator
  
Methods:
  __new__, __init__, __hash__, __repr__, __str__,
  __bool__, __nonzero__, __call__,
  __lt__, __le__, __eq__, __ne__, __ge__, __gt__, __pos__, __neg__,
  __add__, __radd__, __sub__, __rsub__, __mul__, __rmul__,
  __truediv__, __rtruediv__, __div__, __rdiv__, __floordiv__, __rfloordiv__,
  __pow__, __lshift__, __rshift__, derivative"""

  def __new__(cls,a,b=1) :
    if not b : raise ZeroDivisionError;
    a = rationalize(a);
    b = rationalize(b);
    g = a.gcd(b)*b._p[0];    # make denominator monic
    if b == g:
      return a//g;
    self = super(rationalfunction,cls).__new__(cls);
    self._a = a//g;
    self._b = b//g;
    return self;

  def __init__(self,a,b=1) :
    """Do nothing--all the work has been done by __new__"""
    return;

  def __str__(self) :
    return '%s/%s'%(self._a,self._b) if self._b != 1 else str(self._a);

  def __repr__(self) :
    return 'rationalfunction(%s,%s)'%(self._a,self._b);

  @property
  def degree(self) :
    """degree of rational function"""
    return self._a.degree - self._b.degree;

  @property
  def numerator(self) :
    """numerator of rational function"""
    return self._a;

  @property
  def denominator(self) :
    """denominator of rational function"""
    return self._b;

  @property
  def a(self) :
    """numerator of rational function"""
    return self._a;

  @property
  def b(self) :
    """denominator of rational function"""
    return self._b;

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
      if isinstance(other,polynomial) :
        return self._a == self._b*other;
    return self._a*other._b == self._b*other._a;

  def __ne__(self,other) :
    if not isinstance(other,rationalfunction) :
      other = rationalfunction(other);
      if isinstance(other,polynomial) :
        return self._a != self._b*other;
    return self._a*other._b != self._b*other._a;

  def __le__(self,other) :
    if not isinstance(other,rationalfunction) :
      other = rationalfunction(other);
      if isinstance(other,polynomial) :
        return self._a <= self._b*other;
    return self._a*other._b <= self._b*other._a;

  def __lt__(self,other) :
    if not isinstance(other,rationalfunction) :
      other = rationalfunction(other);
      if isinstance(other,polynomial) :
        return self._a < self._b*other;
    return self._a*other._b < self._b*other._a;

  def __ge__(self,other) :
    if not isinstance(other,rationalfunction) :
      other = rationalfunction(other);
      if isinstance(other,polynomial) :
        return self._a >= self._b*other;
    return self._a*other._b >= self._b*other._a;

  def __gt__(self,other) :
    if not isinstance(other,rationalfunction) :
      other = rationalfunction(other);
      if isinstance(other,polynomial) :
        return self._a > self._b*other;
    return self._a*other._b > self._b*other._a;

  def __add__(self,other) :
    if not isinstance(other,rationalfunction) :
      other = rationalfunction(other);      
      if isinstance(other,polynomial) :
        return rationalfunction(self._a+self._b*other,self._b);
    return rationalfunction(self._a*other._b+self._b*other._a,self._b*other._b);

  __radd__ = __add__

  def __sub__(self,other) :
    if not isinstance(other,rationalfunction) :
      other = rationalfunction(other);
      if isinstance(other,polynomial) :
        return rational_function(self._a-self._b*other,self._b);
    return rationalfunction(self._a*other._b-self._b*other._a,self._b*other._b);

  def __rsub__(self,other) :
    if not isinstance(other,rationalfunction) :
      other = rationalfunction(other);
      if isinstance(other,polynomial) :
        return rationalfunction(other*self._b-self._a,self._b);
    return rationalfunction(other._a*self._b-other._b*self._a,self._b*other._b);

  def __mul__(self,other) :
    if not isinstance(other,rationalfunction) :
      other = rationalfunction(other);      
      if isinstance(other,polynomial) :
        return rationalfunction(self._a*other,self._b);
    return rationalfunction(self._a*other._a,self._b*other._b);

  __rmul__ = __mul__

  def __div__(self,other) :
    if not isinstance(other,rationalfunction) :
      other = rationalfunction(other);
      if isinstance(other,polynomial) :
        return rationalfunction(self._a,self._b*other);
    return rationalfunction(self._a*other._b,self._b*other._a);

  def __rdiv__(self,other) :
    if not isinstance(other,rationalfunction) :
      other = rationalfunction(other);
      if isinstance(other,polynomial) :
        return rationalfunction(self._b*other,self._a)
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

  def __lshift__(self,k) :
    """Return self * x**k"""
    if not isint(k) :
      raise TypeError('k must be an integer');
    if k > 0 :
      return rationalfunction(self._a.__lshift__(k),self._b);
    elif k :
      return rationalfunction(self._a,self._b.__lshift(-k));
    else:
      return self;

  def __rshift__(self,k) :
    """Return self * x**-k"""
    return self.__lshift__(-k);

  def derivative(self) :
    """Return derivative of self"""
    return type(self)(
      self._a.derivative()*self._b-self._a*self._b.derivative(), self._b**2);
  
def rationalize(p) :
  """If p is a python number, convert it to a rational or xrational;
     if p is a polynomial with numerical coefficients, convert them all"""
  if isinstance(p,polynomial) :
    types = set();
    for x in p :
      types.add(type(x));
    if set() < types <= REAL and not types <= RATIONAL :
      return p.mapcoeffs(rational);
    elif types <= COMPLEX and not types <= XRATIONAL :
      return p.mapcoeffs(xrational);
  elif type(p) in REAL :
    return polynomial(rational(p));
  elif type(p) in COMPLEX :
    return polynomial(xrational(p));
  return p;

_zero = polynomial();
_one = polynomial(1);
_x = polynomial(1,0);

RATFUN = (polynomial,rationalfunction);
