""" finite field classes """
from __future__ import division

__all__ = ['ffield','ffieldx','conwaypoly']

import sys

import random
random.seed();

from itertools import chain, count
from matrix import matrix, product
from rational import root, rational, rint
from poly import polynomial

from conversions import isint, isstr, isffield, xrange, lmap, bit_length, bit_reverse, bump_bits, zits, stradix, pack, unpack

from numbers import factors, primepower, isirreducible, isirreducible2, irreducibleg, isprimitive, isprimitive2, mpadd, mpmul, mppow, xmpgcd, m2mul, m2sq, m2pow, m2mod, xm2gcd

def __init__(self,x) :
  """Create a finite field element given its polynomial representation, x
The polynomial can be represented as
  a callable, whose value at p gives one of the following
  an integer with absolute value < p**n :
    if nonnegative, x is the value of the polynomial at p
    if negative, -x is the representation of the negative of the field element
  if p <= 36, a string of at most n zits, each having a value < p;
    these values are the polynomial coefficients, ending with the constant;
    the string is stripped and converted to lower case before evaluation;
    zit values are their positions in '0123456789abcdefghijklmnopqrstuvwxyz'
  an iterable of integers, each with absolute value < p
    these (mod p) are the polynomial coefficients, ending with the constant
    the polynomial evaluated at p must be < p**n
Instance variables:
  _p: the characterisitic of the field (inherited from the type)
  _n: the degree of the polynomial modulus (inherited from the type)
  _x: the polynomial representation, evaluated at x=p"""
  p = self._p;
  n = self._n;
  q = self._q;
  try :
    x = x(p);
  except Exception :
    pass;
  if isint(x) :
    if -q < x < q :
      if x < 0 :
        if p == 2 :
          x = -x;
        elif x > -p :
          x += p;
        else :
          x = -x;
          a = [];
          while x :
            a.append(-x%p);
            x //= p;
          for c in reversed(a) :
            x *= p;
            x += c;
      self._x = x;
    else :
      raise ValueError('absolute value must be < %d'%(q));
  elif isstr(x) :
    if p > 36 :    # string not acceptable if p > 36
      raise TypeError('string not acceptable for p > 36');
    s = x.strip().lower();
    x = 0;
    for c in s :
      try :
        x = x*p + zits[:p].index(c);    # will raise ValueError if illegal
      except ValueError :
        raise ValueError('zits in string must be in "%s"'%(zits[:p]));
      if x > q :
        raise ValueError('value must be < %d'%(q));
    self._x = x;
  elif isffield(type(x)) :
    if x.leastfield <= type(self) :
      self._x = x._x;
    else :
      raise TypeError('ffield element must be in field');
  else :
    try :
      c = iter(x);
    except Exception :
      raise TypeError('uninterpretable arg');
    x = 0;
    for i in c :
      if not isint(i) :
        raise TypeError('iterable elements must be integers');
      if not -p < i < p :
        raise ValueError('absolute value of iterable elements must be < %d)'%(p));
      x *= p
      x += i%p;
      if x >= q :
        raise ValueError('value must be < %d'%(q));
    self._x = x;

@property
def element(self) :
  """the field element's representation"""
  return self._x;

@property
def elementtuple(self) :
  """the field element's polynomial representation as a tuple"""
  return unpack(self._basefield._q,self._x);

@property
def elementpolynomial(self) :
  """the field element's polynomial representation"""
  return polynomial(*unpack(self._basefield._q,self._x)).mapcoeffs(self._basefield);

@property
def field_p(self) :
  """the field's characteristic"""
  return self._p;

@property
def field_n(self) :
  """the degree of the field representation's polynomial modulus"""
  return self._n;

@property
def field_q(self) :
  """the size of the field"""
  return self._q;

@property
def field_poly(self) :
  """the field representation's polynomial modulus minus x**n, evaluated at x=p"""
  return self._poly;

@property
def field_fpoly(self) :
  """the field representation's polynomial modulus, evaluated at x=p"""
  return self._p**self._n+self._poly;

@property
def field_tupoly(self) :
  """the field representation's polynomial modulus minus x**n, as a tuple"""
  return self._tupoly[self._nzi:] if self._nzi else ();

@property
def element_order(self) :
  """The multiplicative order of the field element"""
  o = self._q-1;
  if self._x <= 1 :
    return self._x;
  for p in factors(o) :
    while not o%p :
      if (self**(o//p))._x != 1 : break;
      o //= p;
  return o;

@property
def field_ftupoly(self) :
  """the field representation's polynomial modulus, as a tuple"""
  return self._tupoly;

@property
def field_nzi(self) :
  """minus the length of tupoly"""
  return self._nzi;

@property
def field_basefield(self) :
  """the field's base field"""
  return self._basefield;

@property
def generates(self) :
  """True iff self is a generator"""
  o = self._q-1;
  if self._x <= 1 :
    return self._x==o;
  for p in factors(o) :
    if (self**(o//p))._x == 1 : return False;
  return True;

@property
def leastfield(x) :
  """the smallest subfield containing field element x"""
  t = type(x);
  b = t._basefield;
  return b if x._x < b._q else t;

@property
def dfield(self) :
  """Return a superfield with self as _basefield and _n = 2*self._n"""
  t = 2*self._n;
  for i in _ffield.keys() :
    if i[0] == t and i[2] == self.id : return _ffield[i];
  q = self._q;
  o = self(1);
  while True :
    poly = polynomial(o,self(random.randrange(q)),self(random.randrange(1,q)));
    try :
      return ffieldx(poly);
    except Exception :
      continue;

def __hash__(self) :
  return hash(self._x) if self._x < self._p else \
    hash(self.leastfield) ^ hash(self._x);

def __eq__(self,other) :
  """Test if two elements are equal"""
  x = rint(other);
  if isint(x) :
    return 0 <= x < self._p and self._x == x;
  if isffield(type(x)) :
    return self._x == x._x and x.leastfield is self.leastfield;
  return NotImplemented;

def __ne__(self,other) :
  """Test if two elements are unequal"""
  return not self == other;

__le__ = __ge__ = __eq__;
__lt__ = __gt__ = lambda x,y:False;

def __bool__(self) :
  return self._x != 0;

__nonzero__ = __bool__

def __int__(self) :
  """Return self._x if < self._p, else raise TypeError"""
  if self._x < self._p :
    return self._x;
  raise TypeError("can't convert %s element to integer"%(type(self)));

def __str__(self) :
  """Return a string representing the polynomial representation of the finite field element
If n = 1, return the value as a decimal integer, the polynomial evaluated at x=p
Otherwise, return the coefficients in sequence ending with the constant term;
if p <= 36, each coefficient is a zit; else each is a decimal integer, period separated"""
  if self._n == 1 : return '%d'%(self._x);
  return stradix(self._x,self._p,self._n);

def __repr__(self) :
  """Return a string representing the polynomial representation of the finite field element
The string begins with the characterisitic of the field as a decimal integer and is followed
by an underscore and the __str__ representation"""
  return str(self._p)+'_'+str(self);

def __add__(self,other) :
  """Return the sum of the two finite field elements; integers are treated mod p"""
  p = self._p;
  x = self._x;
  if type(other) != type(self) :
    if isffield(type(other)) and other._p == p :
      if self._n == 1 :
        return other+x;
      if other._n == 1 :
        other = other._x;
    other = rint(other);
    if isint(other) :
      if p == 2 :
        return type(self)(x^1) if other&1 else self;
      other %= p;
      return type(self)(x-x%p+(x+other)%p) if other else self;
    return NotImplemented;
  y = other._x;
  if not y : return self;
  if p == 2 :
    return type(self)(x^y);
  if self._n == 1 :
    return type(self)((x+y)%p);
  s = 0;
  P = 1;
  while True :
    x,u = divmod(x,p);
    y,v = divmod(y,p);
    s += (u+v)%p*P;
    if not (x or y) : break;
    P *= p;
  return type(self)(s);

def __pos__(self) :
  """Return the element"""
  return self;

def __neg__(self) :
  """Return the additive inverse of the element"""
  x = self._x;
  if not x : return self;
  p = self._p;
  if p == 2 : return self;
  if self._n == 1 : return type(self)(p-x);
  P = 1;
  y = -x;
  while x :
    P *= p;
    x,r = divmod(x,p);
    if r : y += P;
  return type(self)(y);

def __sub__(self,other) :
  """Return the difference of the two finite field elements; integers are treated mod p"""
  p = self._p;
  x = self._x;
  if type(other) != type(self) :
    if isffield(type(other)) and other._p == p :
      if self._n == 1 :
        return x-other;
      if other._n == 1 :
        other = other._x;
    other = rint(other);
    if isint(other) :
      if p == 2 :
        return type(self)(x^1) if other&1 else self;
      other %= p;
      return type(self)(x-x%p+(x-other)%p) if other else self;
    else :
      return NotImplemented;
  y = other._x;
  if not y : return self;
  if p == 2 : return type(self)(x^y);
  if self._n == 1 : return type(self)((x-y)%p);
  s = 0;
  P = 1;
  while True :
    x,u = divmod(x,p);
    y,v = divmod(y,p);
    s += (u-v)%p*P;
    if not (x or y) : break;
    P *= p;
  return type(self)(s);

def __rsub__(self,y) :
  """Return the difference of the swapped finite field elements; integers are treated mod p"""
  p = self._p;
  y = rint(y);
  if not isint(y) :
    return NotImplemented;
  if p == 2 :
    return type(self)(self._x^1) if y&1 else self;
  y %= p;
  return type(self)(y)-self if y else -self;

def __div__(self,y) :
  """Return the quotient of the two finite field elements; integers are treated mod p"""
  p = self._p;
  x = self._x;
  if type(y) != type(self) :
    if isffield(type(y)) and y._p == p :
      if self._n == 1 :
        return x/y;
      if y._n == 1 :
        y = y._x;
    y = rint(y);
    if isint(y) :
      y %= p;
      if not y : raise ZeroDivisionError;
      if y == 1 : return self;
      d = pow(y,p-2,p);
      s = 0;
      P = 1;
      while True :
        x,r = divmod(x,p);
        s += r*d%p*P;
        if not x : break;
        P *= p;
      return type(self)(s);
    else : return NotImplemented;
  yx = y._x;
  if yx < p : return self/yx;
  if p == 2 : return self*type(self)(xm2gcd(self._fpoly,yx)[2]);
  return self*type(self)(pack(p,xmpgcd(p,self._tupoly,unpack(p,yx))[2]));

def __rdiv__(self,y) :    # y/self
  """Return y/self; y must be an integer and is interpreted mod p"""
  p = self._p;
  y = rint(y);
  if not isint(y) :
    return NotImplemented;
  x = self._x;
  if not x : raise ZeroDivisionError;
  y %= p;
  if not y :
    z = 0;
  elif p == 2 :
    return type(self)(xm2gcd(self._fpoly,x)[2]);
  elif x < p :
    z = y*pow(x,p-2,p)%p;
  else :
    z = 0;
    for i in xmpgcd(p,self._tupoly,unpack(p,x))[2] :
      z = p*z+i*y%p;
  return type(self)(z);

def __mul__(self,y) :
  """Return the product of the two finite field elements; integers are treated mod p"""
  p = self._p;
  x = self._x;
  if type(y) != type(self) :
    if isffield(type(y)) and y._p == p :
      if self._n == 1 :
        return y*x;
      if y._n == 1 :
        y = y._x;
    y = rint(y);
    if isint(y) :
      y %= p;
      if not y : return type(self)(0);
      if y == 1 : return self;
      s = 0;
      P = 1;
      while True :
        x,r = divmod(x,p);
        s += r*y%p*P;
        if not x : break;
        P *= p;
      return type(self)(s);
    else : return NotImplemented;
  if self._n == 1 :
    return type(self)(x*y._x%p);
  if p == 2 :
    y = y._x;
    g = self._poly;
    xy = 0;
    m = M = 1<<(self._n-1);
    N = M-1
    while m :
      xy = ((xy&N)<<1)^g if xy&M else xy<<1;
      if y&m : xy ^= x;
      m >>= 1;
    return type(self)(xy);
  return type(self)(pack(p,mpmul(p,unpack(p,x),unpack(p,y._x),self._tupoly)));

def __pow__(self,e) :
  """Raise the finite field element to the specified power mod p**n-1, 0**0=0"""
  e = rint(e);
  if not isint(e) :
    raise TypeError('power must be integer');
  x = self._x;
  if x <= 1 :
    if x or e > 0 : return self;
    if e : raise ZeroDivisionError;
    return self+1;
  p = self._p;
  o = self._q-1;
  e %= o;
  if e == 0:
    x = 1;
  elif e == 1 :
    return self;
  elif x < p :
    x = pow(x,e,p);
  elif o-e <= o//8 :
    return 1/self**(o-e);
  elif p == 2 :
    g = self._poly;
    f = self._q | g;
    M = 1<<(self._n-1);
    N = M-1;
    n = 1<<(bit_length(e)-2);
    b = x;
    while n :
      z = m2sq(x,f);   # z = x*x mod g
      if e&n :
        x = 0;    # compute x = z*b mod g ...
        m = M;
        while m:
          x = ((x&N)<<1)^g if x&M else x<<1;
          if b&m : x ^= z;
          m >>= 1;
      else :
        x = z;
      n >>= 1;
  else :
    x = pack(p,mppow(p,unpack(p,x),e,self._tupoly));
  return type(self)(x);

def _log(self,base=None,alt=False) :
  """Return the discrete log base base (default: least generator) of self
     if alt, values are signed; always searched by increasing magnitude"""
  x = self._x;
  if x : 
    if base is None :
      base = type(self).generator;
    elif not base :
      raise ValueError('bad base');
    q,r = divmod(base.order,self.order);
    if not r :
      if alt :
        for i,g in enumerate(type(self).iterpow(base**q,alt),1) :
          if g._x == x : return (-(i>>1) if i&1 else (i>>1))*q;
      else :
        for i,g in enumerate(type(self).iterpow(base**q)) :
          if g._x == x : return i*q;
  raise ValueError('not in multiplicative group');  

def _vector(x) :
  """A generator of the coefficients of the polynomial representation"""
  p = x._p;
  n = x._n;
  x = x._x;
  for _ in xrange(n) :
    yield x%p;
    x //= p;

def minpolynomial(self,m=1) :
  """Return, as a polynomial with coeffs in the subfield GF(self._p**m),
the minimal polynomial of self over the subfield.
Raise an exception if m does not divide self._n."""
  return polynomial(*minpoly(self,m));

def minpoly(self,m=1) :
  """Return, as a tuple of elements of the subfield GF(self._p**m),
the coefficients, constant term last, of the minimal polynomial of self
over the subfield. Raise an exception if m does not divide self._n."""
  n = self._n;
  if m <= 0 or n%m : raise ValueError('m must divide self._n');
  G = type(self);
  o = self.order;
  p = self._p;
  G1 = G(1);
  O = p**m-1;    # order of subfield
  if not O%(o or 1) :    # already in subfield
    return (G1,-self);
  d = 1;    # calculate degree of minpoly...
  while (p**(m*d)-1)%o :    # order of element must divide order of subfield
    d += 1;
  if m > 1 :
    # brute force algorithm...
    # ceil(ceil(log(o+1,p))/m) is min possible degree of minpoly
    # n/m is the max possible degree
    G0 = G(0);
    P = [G0]*(n//m) + [G1];    # coeffs of 1, x, x**2, x**3, ... x**(n/m)
    for i in xrange(p,G._q) :  # find generator of superfield of subfield
      g = G(i);
      if not g.order % O: break;
    g **= g.order // O;   # generator of subfield
    P[d] = G1;
    while True :
      # evaluate P(self)
      v = G0;
      for i in xrange(d,0,-1) :
        v = (v+P[i])*self;
      if not O%(v.order or 1) :    # evaluates to element of subfield
        P[0] = -v;
        return tuple(P[d::-1]);
      # try next
      for i in xrange(1,d+1) :
        if P[i] :
          if P[i] == G1 :
            P[i] = G0;
          else :
            P[i] *= g;
            break;
        else:
          P[i] = g;
          break;
      else :
        # d += 1;    # should never happen
        # P[d] = G1;
        raise ValueError('Math failure');
  # get minpoly over GF(p) ...
  X = [];
  x = G1;
  for i in xrange(d) :
    X.append(tuple(map(G,_vector(x))));
    x *= self;
  v = list(_vector(x));    # self**d
  M = matrix(n,d,list(chain.from_iterable(X))).T;
  if n > d :
    for c in reversed(xrange(n)) :  # eliminate redundant columns from M and v
      N = matrix(M);
      del N[:,c];
      if N.rank == d :
        M = N;
        del v[c];
        if len(v) == d : break;
  return (G(1),)+tuple(-(lmap(G,v)*M.inverse))[::-1];

def _create(p,n,poly,x=None) :
  """Return an ffield instance or, if x present, an instance of an ffield instance"""
  F = ffield(p,n,poly);
  return F if x is None else F(x);

def __reduce__(self) :
  """Return a tuple for pickling"""
  return (_create,type(self).id+(self._x,));

_ffield = {}; # (p,n,poly) -> ffield

class ffield(type) :
  """Class to create finite field class for GF(p**n)
Field elements are represented as polynomials over GF(p) with degree < n.
Arithmetic is done modulo a specified irreducible monic polynomial of degree n.
That polynomial modulus is represented as a tuple of coefficients, length <= n,
constant term last; the coefficient of x**n is elided and assumed to be 1 while
immediately following zero coefficients may be elided as well.
The polynomial is also stored as its value at x=p, again without the x**n term.
The polynomial modulus can be specified in either of those ways.
Instance variables (treat as read-only!):
  _p: characteristic (a prime)
  _n: dimension (giving the field p**n elements)
  _q: size of the field (p**n)
  _tupoly: the unelided polynomial modulus as a tuple with first element 1
  _poly: an integer giving the value of the elided polynomial at x = _p
  _fpoly: an integer giving the value of the polynomial modulus at x = _p
  _nzi: minus the length of the tuple representing the elided polynomial modulus
  _basefield: ffield(_p)
Methods: __new__, __init__, __hash__, __eq__, __ne__, __lt__, __le__, __ge__, __gt__,
         __len__, __iter__, __getitem__,  __contains__, iterpow, __reduce__
Descriptors: p, n, q, poly, fpoly, tupoly, ftupoly, id,
             polynomial [modulus of field], basefield,
             order [of field-{0}], generator [of field-{0}]

Signatures:
  ffield(q) : q = p**n, a prime power; use least irreducible polynomial
  ffield(q,n,poly) : q, a prime; n, a positive int; poly, a la tupoly or poly
  ffield(q,n) : q, a prime; n, a positive int; use least irreducible polynomial
  ffield(q,poly) : q, a prime power; poly, a la tupoly or poly
  Note: if poly is specified and not poly, use least irreducible polynomial
   unless p==2 in which case use least irreducible polynomial with fewest 1s

Each instance of the created type is an element of the finite field:
Instance variable (treat as read-only!):
  _x: the value at _p of the polynomial representing the element

Methods: __init__, __hash__, __repr__, __str__, __int__,
         __pos__, __neg__,
         __bool__, __nonzero__, __eq__, __ne__, __lt__, __gt__, __le__, __ge__
         __add__, __radd__, __sub__, __rsub__,
         __mul__, __rmul__, __div__, __rdiv__, __truediv__, __rtruediv__,
         __pow__, log, minpoly, minpolynomial
         __reduce__
Descriptors: [field parameters:] p, n, q, poly, fpoly, ftupoly;
             [element representations:] x, tupoly, polynomial; leastfield
             order [of element], generator [True if element generates]
"""

  def __new__(cls,q,*args,**kwargs) :
    q = primepower(q);
    if not q :
      raise ValueError('Not prime power');
    p,n = q;
    poly = kwargs.pop('poly',None);
    dn = kwargs.pop('n',None);
    if dn != None :
      if n != 1 :
        raise ValueError('n specified for prime power');
      n = dn;
    if len(kwargs) :
      raise TypeError('Allowed keywords: n poly')
    if args :
      if len(args) == 1 :
        if (dn or n != 1) and poly != None :
          raise TypeError('too many arguments');
        x = args[0]
        if n == 1 and isint(x) and x :
          n = x;
        elif poly == None :
          poly = x;
        else :
          raise TypeError('too many arguments');
      elif len(args) == 2 :
        if n != 1 or poly != None :
          raise TypeError('too many arguments');
        n,poly = args;
      else :
        raise TypeError('too many arguments');
    if  n < 1 or not isint(n) :
      raise ValueError('Bad power');
    q = p**n;
    if not poly and n > 1:    # pick least irreducible poly
      if p != 2 :
        d = p if (p-1)%product(factors(n),1 if n&3 else 2) else 0;
        for poly in xrange(1+d+q,q+q) :
          if isirreducible(unpack(p,poly)[1:],p) : break;
        poly -= q;
      elif poly == None :
        for poly in xrange(3,q,2) :
          if isirreducible2(poly|q) : break;
      else :    # with fewest possible bits
        poly = 3;    # first, special case 3 bits, for speed
        for _ in xrange(n>>1) :
          if isirreducible2(q|poly) :
            break;
          poly = (poly<<1)-1;
        else :    # if no irreducibles with 3 bits, try bigger odds
          q1 = q|1;
          hq = q>>1;
          for b in xrange(3,n,2) :    # number of inner bits
            hpoly = (1<<b)-1;    # inner bits
            while hpoly < hq :
              poly = q1|(hpoly<<1);    # only try if poly <= bit_reverse(poly)
              if poly <= bit_reverse(poly) and isirreducible2(poly) :
                poly -= q;
                break;
              hpoly = bump_bits(hpoly);
            else :
              continue; 
            break;
    poly = poly or 0;
    if isint(poly) :
      if not 0 <= poly < q : raise ValueError('Bad poly');
    elif isinstance(poly,tuple) and len(poly) <= n :
      tupoly = poly;
      poly = 0;
      for c in tupoly :
        if not (isint(c) and 0 <= c < p) :
          raise ValueError('Bad poly');
        poly = p*poly + c;
    else : raise ValueError('Bad poly');
    tupoly = unpack(p,poly);
    _nzi = -len(tupoly);
    _tupoly = (1,)+(n+_nzi)*(0,)+tupoly;
    if not isirreducible(_tupoly[1:],p) :
      raise ValueError('Composite poly');
    id = (p,n,poly);
    try :
      return _ffield[id];
    except Exception :
      pass;
    d = dict(_p=p, _n=n, _q=q, _poly=poly, _tupoly=_tupoly, _nzi=_nzi,
             _fpoly=q+poly, p=field_p, n=field_n, q=field_q,
             poly=field_poly, fpoly=field_fpoly, ftupoly=field_ftupoly,
             x=element, tupoly=elementtuple, polynomial=elementpolynomial,
             minpoly=minpoly, minpolynomial=minpolynomial,
             order=element_order, generator=generates, leastfield=leastfield,
             __init__=__init__,
             __repr__=__repr__,
             __str__=__str__,
             __int__=__int__,
             __hash__=__hash__,
             __eq__=__eq__,
             __ne__=__ne__,
             __lt__=__lt__,
             __le__=__le__,
             __gt__=__gt__,
             __ge__=__ge__,
             __bool__ = __bool__,
             __nonzero__=__nonzero__,
             __neg__=__neg__,
             __pos__=__pos__,
             __add__=__add__,
             __radd__=__add__,
             __sub__=__sub__,
             __rsub__=__rsub__,
             __mul__=__mul__,
             __rmul__=__mul__,
             __div__=__div__,
             __truediv__=__div__,
             __rdiv__=__rdiv__,
             __rtruediv__=__rdiv__,
             __pow__=__pow__,
             log = _log,
             __reduce__=__reduce__,
            );

    name = ('GF%d'%(p) if n == 1 and not tupoly else
            'GF%d_%s'%(p,zits[poly] if p <= 36 else str(poly)) if n == 1 else
            'GF%d^%d_%s'%(p,n,''.join([zits[c] for c in tupoly])) if p <= 36 else
            'GF%d^%d_%s'%(p,n,'_'.join(['%d'%(c) for c in tupoly])));
    _ffield[id] = f = type.__new__(cls,name,(),d);
    f._basefield = f if f._n == 1 else ffield(f._p);
    return f;

  def __init__(self,q,*args,**kwargs) :
    return;

  def __reduce__(self) :
    """Return a tuple for pickling"""
    return (_create,self.id);

  def __hash__(self) :
    return hash(type(self))^hash(self.id);

  def __eq__(self,other) :
    return self is other;
  
  def __ne__(self,other) :
    return not self is other;

  def __le__(self,other) :
    if isinstance(other,ffield) :
      return self is other or self is other._basefield;
    return NotImplemented;

  def __ge__(self,other) :
    return other <= self;

  def __lt__(self,other) :
    if isinstance(other,ffield) :
      return not self is other and self is other._basefield;
    return NotImplemented;

  def __gt__(self,other) :
    return other < self;

  def __bool__(self) :
    return True;

  __nonzero__ = __bool__

  def __len__(self) :
    """Return p**n, the size of the field"""
    return self._q;

  def __iter__(self) :
    """Return an iterator for the elements of the field"""
    return (self(x) for x in xrange(self._q));

  def __getitem__(self,key) :
    """Return tuple(self)[key]"""
    if isint(key) :
      q = self._q;
      if -q <= key < q :
        return self(key%q);
      raise IndexError('index out of range');
    elif isinstance(key,slice) :
      return tuple(self(i) for i in xrange(*key.indices(self._q)));
    raise IndexError('index must be integer or slice');

  def __contains__(self,x) :
    """Return True iff x is an element of the field"""
    return isint(rint(x)) and abs(x) < self._p or \
           isffield(type(x)) and x.leastfield <= self;

  def iterpow(self,x=0,alt=False) :
    """Return an iterator of the powers of x, or powers of smallest generator
       power sequence: 0,1,2,..., or, if alt, 0,1,-1,2,-2,..."""
    if not x :
      x = self.generator;
    if alt :
      def g(f) :
        e = x;
        y = 1/x;
        while True :
          yield f;
          if e._x == f._x : break;
          yield e;
          e *= x;
          if e._x == f._x : break;
          f *= y;
    else :
      def g(e) :
        while True :
          yield e;
          e *= x;
          if e._x <= 1 : break;
    return g(self(1));

  p = field_p;
  n = field_n;
  q = field_q;
  poly = field_poly;
  fpoly = field_fpoly;
  tupoly = field_tupoly;
  ftupoly = field_ftupoly;
  basefield = field_basefield;

  @property
  def polynomial(self) :
    """the polynomial modulus"""
    return polynomial(*self._tupoly).mapcoeffs(self._basefield);

  @property
  def order(self) :
    """p**n-1, the multiplicative order of the field"""
    return self._q-1;

  @property
  def generator(self) :
    """the "smallest" generator of the field"""
    try :
      return self.__generator;
    except AttributeError :
      for g in self :
        if g.generator :
          self.__generator = g;
          return g;

  @property
  def id(self) :
    """the ID of the field: (_p,_n,_poly)"""
    return (self._p,self._n,self._poly);

  def foo(self,foo=None) :
    raise AttributeError("type object '%s' has no Attribute 'x'"%(self.__name__));

  x = property(foo,foo,foo);
  del foo;

  dfield = dfield;

def _x(x) :
  """Return _x attribute"""
  return x._x;

def r__init__(self,x) :
  """Create a finite field element given its polynomial representation, x
The polynomial can be represented as
  a polynomial with coefficients each a representation of a subfield element
  an integer with absolute value < q = p**n :
    if nonnegative, x is the packed value
    if negative, -x is the representation of the negative of the field element
  if p <= 36, a string of at most n zits, each having a value < p;
    the string is stripped and converted to lower case before evaluation;
    zit values are their positions in '0123456789abcdefghijklmnopqrstuvwxyz'
    The result is converted as a base p number, resulting in x.
  an iterable of subfield elements and/or integers, with abs value of integers < basefield.q
    each integer must have absvalue < basefield.q and if negative represents the
    negative of the subfield element that is represented by its absolute value
    
Instance variables:
  _p: the characterisitic of the field (inherited from the type)
  _n: the degree of the polynomial modulus (inherited from the type)
  _x: the packed polynomial representation"""
  p = self._p;
  n = self._n;
  q = self._q;
  s = self._basefield;
  r = s._q;
  try :
    x = x(r);
  except Exception :
    pass;
  if isint(x) :
    if -q < x < q :
      if x < 0 :
        if p == 2 :
          x = -x;
        elif x > -p :
          x += p;
        else :
          x = -x;
          a = [];
          while x :
            a.append(-x%p);
            x //= p;
          for c in reversed(a) :
            x *= p;
            x += c;
      self._x = x;
    else :
      raise ValueError('absolute value must be < %d'%(q));
  elif isstr(x) :
    if p > 36 :    # string not acceptable if p > 36
      raise TypeError('string not acceptable for basefield.q > 36');
    s = x.strip().lower();
    x = 0;
    for c in s :
      try :
        x = x*p + zits[:p].index(c);    # will raise ValueError if illegal
      except ValueError :
        raise ValueError('zits in string must be in "%s"'%(zits[:p]));
      if x > q :
        raise ValueError('value must be < %d'%(q));
    self._x = x;
  elif isffield(type(x)) :
    if x.leastfield <= type(self) :
      self._x = x._x;
    else :
      raise TypeError('ffield element must be in field');
  else :
    try :
      c = iter(x);
    except Exception :
      raise TypeError('uninterpretable arg');
    x = 0;
    for i in c :
      i = rint(i);
      if isint(i) :
        if -r < i < r :
          i = -s(-i) if i<0 else s(i);
        else :
          raise TypeError('iterable elements must be elements of subfield');
      if isffield(type(i)) :
        if not i in self._basefield :
          raise TypeError('iterable elements must be elements of subfield');
        i = i._x;
      x = x*r+i;
      if x >= q :
        raise ValueError('value must be < %d'%(q));
    self._x = x;

@property
def rleastfield(x) :
  """the smallest subfield containing field element x"""
  t = type(x);
  while t._n > 1 and x._x < t._basefield._q : t = t._basefield;
  return t;

@property
def rgenerates(self) :
  if self._x < self._basefield._q :
    return False;
  o = self._q-1;
  for p in factors(o) :
    if (self**(o//p))._x == 1 : return False;
  return True;

def r__str__(self) :
  """Return a string representing the polynomial representation of the finite field element:
the coefficients' basefield representations in sequence ending with the constant term"""
  return stradix(self._x,self._p,self._n);

def r__repr__(self) :
  """Return a string representing the polynomial representation of the finite field element
in the form p^n_s, where p^n is the order of the basefield and s = str(self)""" 
  return str(self._p)+'^'+str(self._basefield._n)+'_'+str(self);

def r__add__(self,other) :
  """Return the sum of the two finite field elements; integers are treated mod p"""
  p = self._p;
  x = self._x;
  if type(other) != type(self) :
    if isffield(type(other)) and other._p == p :
      if other._n == 1 :
        other = other._x;
    other = rint(other);
    if isint(other) :
      if p == 2 :
        return type(self)(x^1) if other&1 else self;
      other %= p;
      return type(self)(x-x%p+(x+other)%p) if other else self;
    elif other not in self._basefield :
      return NotImplemented;
  y = other._x;
  if not y : return self;
  if p == 2 :
    return type(self)(x^y);
  s = 0;
  P = 1;
  while True :
    x,u = divmod(x,p);
    y,v = divmod(y,p);
    s += (u+v)%p*P;
    if not (x or y) : break;
    P *= p;
  return type(self)(s);

def r__sub__(self,other) :
  """Return the difference of the two finite field elements; integers are treated mod p"""
  p = self._p;
  x = self._x;
  if type(other) != type(self) :
    if isffield(type(other)) and other._p == p :
      if other._n == 1 :
        other = other._x;
    other = rint(other);
    if isint(other) :
      if p == 2 :
        return type(self)(x^1) if other&1 else self;
      other %= p;
      return type(self)(x-x%p+(x-other)%p) if other else self;
    elif other not in self._basefield :
      return NotImplemented;
  y = other._x;
  if not y : return self;
  if p == 2 : return type(self)(x^y);
  s = 0;
  P = 1;
  while True :
    x,u = divmod(x,p);
    y,v = divmod(y,p);
    s += (u-v)%p*P;
    if not (x or y) : break;
    P *= p;
  return type(self)(s);

def r__rsub__(self,y) :
  """Return the difference of the swapped finite field elements; integers are treated mod p"""
  p = self._p;
  y = rint(y);
  if not isint(y) :
    if y in self._basefield :
      if p == 2 :
        return type(self)(self._x^y._x) if y._x else self;
      return type(self)(y)-self if y else -self;
    return NotImplemented;
  if p == 2 :
    return type(self)(self._x^1) if y&1 else self;
  y %= p;
  return type(self)(y)-self if y else -self;

def r__mul__(self,y) :
  """Return the product of the two finite field elements; integers are treated mod p"""
  p = self._p;
  x = self._x;
  if type(y) != type(self) :
    if isffield(type(y)) and y._p == p :
      s = self._basefield;
      if y in s :
        if y._n == 1 :
          y = y._x;
        else :
          y = s(y._x);
          f = lambda x: (s(x)*y)._x;
          q = s._q;
          return type(self)(pack(q,map(f,unpack(q,x))));
    y = rint(y);
    if isint(y) :
      y %= p;
      if not y : return type(self)(0);
      if y == 1 : return self;
      s = 0;
      P = 1;
      while True :
        x,r = divmod(x,p);
        s += r*y%p*P;
        if not x : break;
        P *= p;
      return type(self)(s);
    else : return NotImplemented;
  s = self._basefield;
  q = s._q;
  xt = polynomial(*map(s,unpack(q,x)));
  yt = polynomial(*map(s,unpack(q,y._x)));
  zt = (xt*yt)%self._polynomial;
  return type(self)(pack(q,map(_x,zt[::-1])));

def r__div__(self,y) :
  """Return the quotient of the two finite field elements; integers are treated mod p"""
  if not y : raise ZeroDivisionError;
  p = self._p;
  x = self._x;
  if type(y) != type(self) :
    if isffield(type(y)) and y._p == p :
      if y._n == 1 :
        y = y._x;
      elif y in self._basefield :
        return self*(1/y);
    y = rint(y);
    if isint(y) :
      y %= p;
      if y == 1 : return self;
      d = pow(y,p-2,p);
      s = 0;
      P = 1;
      while True :
        x,r = divmod(x,p);
        s += r*d%p*P;
        if not x : break;
        P *= p;
      return type(self)(s);
    else : return NotImplemented;
  yx = y._x;
  if yx < p : return self/yx;
  s = self._basefield;
  q = s._q;
  yt = polynomial(*map(s,unpack(q,yx)));
  return self*type(self)(pack(q,map(_x,self._polynomial.xgcd(yt)[2][::-1])));

def r__rdiv__(self,y) :    # y/self
  """Return y/self; y must be in subfield, or an integer interpreted mod p"""
  if not self : raise ZeroDivisionError;
  p = self._p;
  y = rint(y);
  if not isint(y) :
    if y in self._basefield :
      return 1/self*y;
    else :
      return NotImplemented;
  x = self._x;
  y %= p;
  if not y :
    z = 0;
  elif x < p :
    z = y*pow(x,p-2,p)%p;
  else :
    s = self._basefield;
    q = s._q;
    xt = polynomial(*map(s,unpack(q,x)));
    z = 0;
    for i in unpack(p,pack(q,map(_x,self._polynomial.xgcd(xt)[2][::-1]))) :
      z = p*z+i*y%p;
  return type(self)(z);

def r__pow__(self,e) :
  """Raise the finite field element to the specified power mod p**n-1, 0**0=0"""
  e = rint(e);
  if not isint(e) :
    raise TypeError('power must be integer');
  x = self._x;
  if x <= 1 :
    if x or e > 0 : return self;
    if e : raise ZeroDivisionError;
    return self+1;
  p = self._p;
  o = self._q-1;
  e %= o;
  if e == 0:
    x = 1;
  elif e == 1 :
    return self;
  elif x < p :
    x = pow(x,e,p);
  elif o-e <= o//8 :
    return 1/self**(o-e);
  else :
    s = self._basefield;
    q = s._q;
    xt = polynomial(*map(s,unpack(q,x)));
    x = pack(q,map(_x,xt.__pow__(e,self._polynomial)[::-1]));
  return type(self)(x);

class ffieldx(type) :
  """Class to create finite field extension class.
The finite field G is defined by a degree k>1 irreducible polynomial (poly) with
coefficients in a finite field F. Elements of G are represented by tuples of
k elements of F. If len(F) = p**j, then each element of F can be represented as
a nonegative integer < p**j, and each element of G can be represented as a
nonnegative integer < p**(j*k), the evaluation of the polynomial at p**k when
treating each coefficient as its integer representation.
Elements of G are polynomials over GF(p**j) mod poly.
  _p: characteristic (a prime)
  _n: dimension (giving the field p**n elements) (j*k)
  _q: size of the field (p**n)
  _polynomial: the polynomial modulus, coefficients in _basefield
  _basefield: the subfield of which this field is an extension
  _poly: the packed polynomial modulus, with leading term elided
Methods: __new__, __init__, __hash__, __eq__, __ne__, __lt__, __le__, __ge__, __gt__,
         __len__, __iter__, __getitem__,  __contains__, iterpow, __reduce__

Descriptors: p, n, polynomial [modulus of field extension], basefield,
             order [of field-{0}], generator [of field-{0}], id

Signatures:
  ffieldx(poly) : poly an irreducible monic poly with coefficients in some finite field

Methods: __init__, __hash__, __repr__, __str__, __int__,
         __pos__, __neg__,
         __bool__, __nonzero__, __eq__, __ne__, __lt__, __gt__, __le__, __ge__
         __add__, __radd__, __sub__, __rsub__,
         __mul__, __rmul__, __div__, __rdiv__, __truediv__, __rtruediv__,
         __pow__

Descriptors: [field parameters:] p, n, q;
             [element representations:] x, tupoly, polynomial; leastfield,
             order [of element], generator [True if element generates]
"""

  def __new__(cls,poly) :
    i = 0;
    subfield = None;
    for c in poly :
      c = rint(c);
      t = type(c);
      if isint(c) :
        i = max(i,abs(c));
      elif isffield(t) :
        if not subfield or t > subfield : subfield = t;
        elif not t <= subfield :
          raise TypeError('all coeffs must be in same field');
      else :
        raise TypeError('all coeffs must be field elements');
    if not subfield :
      raise TypeError('at least one coeff must be a field element');
    p = subfield._p;
    if i >= p :
      raise TypeError('integer coeffs must be in GF(p)')
    poly = poly.mapcoeffs(subfield);
    if poly[-1] != 1 or not poly.isirreducible() :
      raise ValueError('poly not monic irreducible');
    d = poly.degree;
    if d == 1 : return subfield;
    _poly = pack(subfield._q,map(_x,poly[d-1::-1]));
    m = subfield._n;
    if m == 1 : return ffield(p,d,_poly);
    n = d*m;
    q = p**n;
    id = (n,_poly,subfield.id);
    try :
      return _ffield[id];
    except Exception :
      pass;
    d = dict(_p=p, _n=n, _q=q, _basefield = subfield, _polynomial = poly,
             p=field_p, n=field_n, q=field_q, _poly = _poly,
             x=element, tupoly=elementtuple, polynomial=elementpolynomial,
             minpoly=minpoly, minpolynomial=minpolynomial,
             order=element_order,generator=rgenerates, leastfield=rleastfield,
             __init__=r__init__,
             __repr__=r__repr__,
             __str__=r__str__,
             __int__=__int__,
             __hash__=__hash__,
             __eq__=__eq__,
             __ne__=__ne__,
             __lt__=__lt__,
             __le__=__le__,
             __gt__=__gt__,
             __ge__=__ge__,
             __bool__ = __bool__,
             __nonzero__=__nonzero__,
             __neg__=__neg__,
             __pos__=__pos__,
             __add__=r__add__,
             __radd__=r__add__,
             __sub__=r__sub__,
             __rsub__=r__rsub__,
             __mul__=r__mul__,
             __rmul__=r__mul__,
             __div__=r__div__,
             __truediv__=r__div__,
             __rdiv__=r__rdiv__,
             __rtruediv__=r__rdiv__,
             __pow__=r__pow__,
             log = _log,
#             __reduce__=__reduce__,
            );

    name = ('GF%d^%d>%s:%s'%(p,n,subfield.__name__,'_'.join(['%s'%(c) for c in poly.mapcoeffs(_x)])));
    _ffield[id] = f = type.__new__(cls,name,(),d);
    return f;

  def __hash__(self) :
    return hash(type(self))^hash(self.id);

  def __eq__(self,other) :
    return self is other;
  
  def __ne__(self,other) :
    return not self is other;

  def __le__(self,other) :
    if isffield(other) :
      return self is other or other is not other._basefield >= self;
    return NotImplemented;

  def __ge__(self,other) :
    if isffield(other) :
      return self is other or self._basefield >= other;
    return NotImplemented;

  def __lt__(self,other) :
    if isffield(other) :
      return not other is other.basefield and self <= other._basefield;
    return NotImplemented;

  def __gt__(self,other) :
    if isffield(other) :
      return not self is other and self._basefield >= other;
    return NotImplemented;

  def __bool__(self) :
    return True;

  __nonzero__ = __bool__

  def __len__(self) :
    """Return p**n, the size of the field"""
    return self._q;

  def __iter__(self) :
    """Return an iterator for the elements of the field"""
    return (self(x) for x in xrange(self._q));

  def __getitem__(self,key) :
    """Return tuple(self)[key]"""
    if isint(key) :
      q = self._q;
      if -q <= key < q :
        return self(key%q);
      raise IndexError('index out of range');
    elif isinstance(key,slice) :
      return tuple(self(i) for i in xrange(*key.indices(self._q)));
    raise IndexError('index must be integer or slice');

  def __contains__(self,x) :
    """Return True iff x is an element of the field"""
    return isint(rint(x)) and abs(x) < self._p or \
           isffield(type(x)) and x.leastfield <= self;

  def iterpow(self,x=0,alt=False) :
    """Return an iterator of the powers of x, or powers of smallest generator
       power sequence: 0,1,2,..., or, if alt, 0,1,-1,2,-2,..."""
    if not x :
      x = self.generator;
    if alt :
      def g(f) :
        e = x;
        y = 1/x;
        while True :
          yield f;
          if e._x == f._x : break;
          yield e;
          e *= x;
          if e._x == f._x : break;
          f *= y;
    else :
      def g(e) :
        while True :
          yield e;
          e *= x;
          if e._x <= 1 : break;
    return g(self(1));

  p = field_p;
  n = field_n;
  q = field_q;
  basefield = field_basefield;

  @property
  def polynomial(self) :
    """the polynomial modulus"""
    return self._polynomial;

  @property
  def tupoly(self) :
    """the elided polynomial modulus"""
    s = self._polynomial;
    n = -len(s);
    for i,c in enumerate(s,n+1) :
      if i and c : n = i;
    return s.mapcoeffs(lambda x: x._x)[n-1::-1];

  @property
  def order(self) :
    """p**n-1, the multiplicative order of the field"""
    return self._q-1;

  @property
  def generator(self) :
    """the "smallest" generator of the field"""
    try :
      return self.__generator;
    except AttributeError :
      for x in xrange(self._basefield._q,self._q) :
        g = self(x);
        if g.generator :
          self.__generator = g;
          return g;

  @property
  def id(self) :
    """the ID of the field"""
    return (self._n,self._poly,self._basefield.id);

  def foo(self,foo=None) :
    raise AttributeError("type object '%s' has no Attribute 'x'"%(self.__name__));

  x = property(foo,foo,foo);
  del foo;

  dfield = dfield;


"""The Conway polynomial for q = p^n is the "least" degree n primitive GF(p) polynomial
g_{q} such that if n/m is a prime, g_{q}(x) | g_{p^m}(x^((p^n-1)/(p^m-1))}.
The ordering of polynomials x^n - a_{n-1}x^(n-1) + a_{n-2}x^(n-2) ... (-1)^n a_0
is lexicographically by a_{n-1} a_{n-2} ... a_0."""

_cpdict = {};    # q -> packed Conway polynomial for GF(q) with leading term elided

def conwaypoly(q) :
  """Return the Conway polynomial for GF(q) as a packed GF(p) polynomial,
  where q = p**n, with the coefficient of x**n elided"""
  try :
    return _cpdict[q];
  except Exception :
    pass;
  try :
    p,n = primepower(q);
  except Exception :
    raise ValueError('Not prime power');
  if p == 2 :
    for g in xrange(1,q,2) :
      gq = g|q;
      if isirreducible2(gq) and isprimitive2(gq) :
        for f in factors(n) :
          m = n//f;
          r = 1<<m;
          d = (q-1)//(r-1);
          c = conwaypoly(r);
          xd = m2pow(2,d,gq);
          b = 1<<bit_length(c)>>2;
          a = 1;
          while b :
            a = m2mod(m2mul(a,xd),gq);
            if b&c : a ^= 1;
            b >>= 1;
          if m2pow(2,d*m,gq)^a : break;
        else :
          _cpdict[q] = g;
          return g;
  else :
    for g in irreducibleg(p,n) :
      # modify g by negating alternate terms
      g = tuple(-g[i]%p if i&1 else g[i] for i in xrange(n+1));
      if not isprimitive(g[1:],p) : continue;
      x = (1,0);
      for f in factors(n) :
        m = n//f;
        r = p**m;
        d = (q-1)//(r-1);
        c = unpack(p,conwaypoly(r));
        xd = mppow(p,x,d,g);
        s = [];
        for a in c :
          s = mpmul(p,s,xd,g,a);
        if mpadd(p,mppow(p,x,d*m,g),s) : break;
      else :
        _cpdict[q] = c = pack(p,g[1:]);
        return c;
  raise SystemError('Did not find Conway polynomial');
