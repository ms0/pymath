from __future__ import division

__all__ = ['polynomial','rationalfunction']

import sys

from itertools import chain, count
from collections import defaultdict
from matrix import product, bmatrix
from rational import rational,xrational,inf
import ffield as ff
from random import randrange,randint

if sys.version_info>(3,) :
  xrange = range;
  iteritems = lambda x: x.items();
  isint = lambda x: isinstance(x,int);
  INT = set((int,));
  REAL = set((int,float,rational));
else :
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
except Exception :
  import math
  def bit_length(n) :
    n = abs(n);
    b = 0;
    while n :
      try :
        l = int(math.log(n,2));
        while n >> l : l += 1;
      except OverflowError :
        l = sys.float_info.max_exp-1;
      b += l
      n >>= l;
    return b;

int_float = lambda x: x if isint(x) else x.a if abs(x.b)==1 else float(x);
floatall = lambda x: x.mapcoeffs(int_float);
complexall = lambda x: x.mapcoeffs(complex);
identity = lambda x: x;

def leastfactor(n,maxfactor=None) :
  for p in ff.factors(n,maxfactor) :
    return p;
  return 1;

# danger: division converts to floating point (unless we use rational coeffs)

def nzpolymul(f,g) :
  fg = (len(f)+len(g)-1)*[0*f[0]];
  for i in xrange(len(f)) :
    for j in xrange(len(g)) :
      fg[i+j] += f[i]*g[j];
  return fg;

def nzpolypow(b,e,m=None) :
  n = (1 << (bit_length(e)-1)) >> 1;
  if m :
    x = b = nzpolydivrem(b,m)[1];
    while n :
      x = nzpolydivrem(nzpolymul(x,x),m)[1];
      if e&n :
        x = nzpolydivrem(nzpolymul(x,b),m)[1];
      n >>= 1;
  else :
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
  __init__, __hash__, __repr__, __str__,
  __bool__, __nonzero__, __len__, __iter__, __call__,
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
    return self.__class__(*tuple(-cs for cs in self._p));

  def __add__(self,other) :
    """Return the sum self+other"""
    if not isinstance(other,self.__class__) :
      if isinstance(other,rationalfunction) : return other+self;
      other = self.__class__(other);
    if len(self._p) < len(other._p) : self,other = other,self;
    d = len(self._p) - len(other._p);
    return self.__class__(*tuple(cs if i<0 else cs+other._p[i] for i,cs in enumerate(self._p,-d)));

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
    if not isinstance(other,self.__class__) :
      if isinstance(other,rationalfunction) : return other*self;
      other = self.__class__(other);
    return self.__class__(*nzpolymul(self._p,other._p));

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
        other = self.__class__(other);
    if not self._p : return self;
    return self.__class__(*(nzpolydivrem(self._p,other._p)[0]));

  def __rfloordiv__(self,other) :
    """Return the quotient other//self"""
    if not self._p : raise ZeroDivisionError;
    if not other : return _zero;
    return self.__class__(other)//self;

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
          return other.__rdiv__(self),_zero;
        other = other._a;
      else :
        other = self.__class__(other);
    q,r = nzpolydivrem(self._p,other._p);
    return self.__class__(*q),self.__class__(*r);

  def __rdivmod__(self,other) :
    """Return the quotient and remainder when dividing other by self"""
    if not self._p : raise ZeroDivisionError;
    if not other : return _zero,_zero;
    return divmod(self.__class__(other),self);

  def __mod__(self,other) :
    """Return the remainder when dividing self by other"""
    if not other : raise ZeroDivisionError;
    if not self._p : return self;
    if not isinstance(other,self.__class__) :
      if isinstance(other,rationalfunction) :
        if other._b == 1 :
          other = other._a;
        return _zero;
      else :
        other = self.__class__(other);
    return self.__class__(*(nzpolydivrem(self._p,other._p)[1]));

  def __rmod__(self,other) :
    """Return the remainder when dividing other by self"""
    if not self._p : raise ZeroDivisionError;
    if not other : return _zero;
    return self.__class__(other)%self;

  def __pow__(self,e,m=None) :
    """Return self raised to integer e: self**e; if m, mod polynomial m"""
    if not isint(e) :
      raise TypeError('exponent must be an integer');
    if not (m is None or isinstance(m,polynomial) and m.degree > 0) :
      raise TypeError('modulus must be polynomial of degree > 0')
    if self.degree <= 0 :
      return self.__class__(self[0]**e);
    if e <= 0:
      if e :
        if m :
          raise ValueError('2nd arg cannot be negative when 3rd arg specified');
        return rationalfunction(self[self.degree].__class__(1),self.__class__(*nzpolypow(self._p,-e)));
      return self.__class__(self[self.degree].__class__(1));
    return self.__class__(*nzpolypow(self._p,e,m and m._p));

  def derivative(self,k=1) :    # kth derivative
    """Return the kth derivative of self"""
    if not (isint(k) and k >= 0) :
      raise TypeError('kth derivative only defined for k nonegative integer');
    d = len(self._p);
    return self.__class__(*tuple(product(xrange(d-i,d-i-k,-1),c)
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

  def isirreducible(self,q=0) :
    """Return True iff self is irreducible over a field;
if q is specified, it is the size of the field;
if q is not specified, the field is inferred from self's coefficients"""
    if q :
      r = ff.primepower(q);
      if not r :
        raise ValueError('q must be a prime power')
    d = self.degree;
    if d <= 1 :
      return True;
    types = set();
    for x in self :
      types.add(x.__class__);
    if types <= INT and q > 0:
      r = r[0];
      if self._p[0] != 1 :
        i = ff.modpow(self._p[0],r-2,r);    # make monic
        self = self.mapcoeffs(lambda x: x*i%r);
        if d != self.degree :
          raise ValueError('leading coefficient is 0 mod %d'%(r));
      return ff.isirreducible(self._p[1:],q);
    if len(types) == 1 and type(tuple(types)[0]) == ff.ffield :
      p0 = self._p[0];
      if int(p0) != 1 :
        self = self.mapcoeffs(lambda x: x/p0);    # make monic
      q = q or p0.p**p0.n;
      for c in self :
        if (q-1)%(c.order or 1) :
          raise ValueError('coefficients not all elements of GF(%d)'%(q));
      x = self.__class__(self._p[0],self._p[0]*0);    # Rabin test...
      for s in chain(ff.factors(d),(1,)) :
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
    raise TypeError('implemented only for finite fields');

  def factor(self,facdict=None,e=1) :
    """Return a factorization of polynomial self as a defaultdict(int);
keys are factors, and values are positive integer exponents;
if the leading coefficient is real (i.e., int or float),
the coefficients are converted to rationals before factoring
and the result's coefficients are converted to ints if integers else floats.
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
          facdict[self.__class__(int_float(f))] += 1;
      return facdict;
    elif types <= COMPLEX and not types <= XRATIONAL :
      for k,v in iteritems(self.mapcoeffs(xrational).factor()) :
        facdict[k.mapcoeffs(complex)] += v;
      return facdict;
    if self._p[0]**2 != self._p[0] :
      facdict[self.__class__(self._p[0])] += e;
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
      return self.__class__(*(x**px for x in g._p[::p])).factor(facdict,p*e);
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
        h = b = self.__class__(o,z);    # compute x**q**i % self ...
        x = q**i;
        m = (1<<(bit_length(x)-1)) >> 1;
        while m :
          h = h*h%self;
          if x&m :
            h = self.__class__(*h._p+(z,))%self;
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
              c = ff.ffield(q);
              z = c(0);
              o = c(1);
              maps = fieldmaps(saved[0],c);
              g = g.mapcoeffs(maps[0]);
              f = set((g,));
            else :
              saved = ();
            x = (q**i-1)//leastfactor(q**i-1);
            while len(f) < r :
              h = b = self.__class__(o,
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
              f = map(lambda x:x.mapcoeffs(maps[1]),f);
          for u in f :
            facdict[u] += e;
        i += 1;
      if self.degree :
        facdict[self] += e;     # must be irreducible
    except AttributeError :
      if not self._p[-1] :    # self(0) == 0
        facdict[self.__class__(self._p[0],self._p[-1])] += e;    # add x as factor
        self = self.__class__(*self._p[:-1]);    # divide by x
      if isinstance(self._p[0],rational) :
        m = ff.lcma(map(lambda x:x.denominator,self._p));
        if m != 1 : facdict[self.__class__(rational(1,m))] += e;
        self = self.mapcoeffs(lambda x:m*x);
        m = 1;    # combine constant factors
        i = [];
        for f,k in facdict.items() :
          if f.degree == 0 :
            i.append(f);
            m *= f._p[0]**k;
        for f in i : del facdict[f];
        if m != 1 : facdict[self.__class__(m)] += 1;
        t = set();        # look for linear factors
        while self.degree > 1 :
          for a in ff.divisors(int(self._p[0])) :
            for b in ff.divisors(int(self._p[-1])) :
              r = rational(b,a);
              if r not in t :
                t.add(r);
                if not self(r) :
                  f = self.__class__(a,-b);
                  facdict[f] += e;
                  self /= f;
                  break;
              r = rational(-b,a);
              if r not in t :
                t.add(r);
                if not self(r) :
                  f = self.__class__(a,b);
                  facdict[f] += e;
                  self /= f;
                  break;
            else : continue;
            break;
          else : break;
      facdict[self] += e;

  def mapcoeffs(self,f) :
    """Apply f to each coefficient and return the resulting polynomial"""
    return self.__class__(*map(f,self._p));

  @staticmethod
  def unfactor(facdict,p=None) :
    """Take a factorization as produced by factor() and return the product,
multiplied by p if specified"""
    if p == None : p = _one;
    for f,e in iteritems(facdict) :
      p *= f**e;
    return p;

def fieldmaps(F,G) :    # F and G are fields, F.p == G.p == 2, 2*F.n == G.n
  if F.n == 1 :
    return (G,F);
  fp = F.polynomial;    #F(2).minpoly();
  m = F.n;
  n = G.n;
  while True :    # find generator of G
    g = G(randrange(2,2**n));
    if g.order==G.order : break;
  h = g**(G.order//F.order);    # generator of F in G
  for x in xrange(1,F.order-1) :
    j = h**x;
    if not fp(j) : break; # find an x such that h**x has minpoly F.ftupoly
  F2G = lambda f: f.polynomial(j);
  v = [G(1),j];
  p = j;
  for i in xrange(2,m) :
    p *= j;
    v.append(p);
  p = g;
  for k in xrange(1,2) :
    for i in xrange(m) :
      v.append(v[(k-1)*2+i]*g);
      p *= g;
  # v has n entries, but each needs to be turned into a column
  s = 0;
  for x in v[::-1] :
    s = (s<<n) | x.x;
  M = bmatrix((n,n),s).T.inverse[:,:m];
  G2F = lambda g: F((bmatrix((n,),g.x)*M)._bits);
  return (F2G,G2F);

class rationalfunction() :
  def __init__(self,a,b=1) :
    if not b : raise ZeroDivisionError;
    a = rationalize(a);
    b = rationalize(b);
    g = a.gcd(b)*b._p[0];    # make denominator monic
    self._a = a//g;
    self._b = b//g;

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

def irreducibles(q,n) :
  """Return a tuple of all monic irreducible degree n polynomials over F;
  F is q if q is an ffield; else q must be a prime power, and F=ffield(q)"""
  return tuple(irreducibleg(q,n));

def irreducibleg(q,n) :
  """Generate all monic irreducible degree n polynomials over F;
  F is q if q is an ffield; else q must be a prime power, and F=ffield(q)"""
  if isinstance(q,ff.ffield) :
    F = q;
    q = F.__len__();
  else :
    F = ff.ffield(q);
  for i in range(q**n) :
    poly = [F(1)];
    j = i;
    for k in range(n) :
      poly.append(F(j%q));
      j //= q;
    poly = polynomial(*poly);
    if poly.isirreducible() : yield poly;
