from __future__ import division

__all__ = ['ffieldx']

from ffield import xrange, ffield, _ffield, primepower, pack, unpack, rint, isffield, isint, isstr, stradix, zits, factors, minpoly, minpolynomial
from poly import *

def _x(x) :
  """Return _x attribute"""
  return x._x;

def __init__(self,x) :
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
def field_basefield(self) :
  """the field's base field GF(p)"""
  return self._basefield;

@property
def leastfield(x) :
  """the smallest subfield containing field element x"""
  t = type(x);
  while t._n > 1 and x._x < t._basefield._q : t = t._basefield;
  return t;

@property
def generates(self) :
  if self._x < self._basefield._q :
    return False;
  o = self._q-1;
  for p in factors(o) :
    if (self**(o//p))._x == 1 : return False;
  return True;

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
  """Return a string representing the polynomial representation of the finite field element:
the coefficients' basefield representations in sequence ending with the constant term"""
  return stradix(self._x,self._p,self._n);

def __repr__(self) :
  """Return a string representing the polynomial representation of the finite field element
in the form p^n_s, where p^n is the order of the basefield and s = str(self)""" 
  return str(self._p)+'^'+str(self._basefield._n)+'_'+str(self);

def __add__(self,other) :
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

def __pos__(self) :
  """Return the element"""
  return self;

def __neg__(self) :
  """Return the additive inverse of the element"""
  x = self._x;
  if not x : return self;
  p = self._p;
  if p == 2 : return self;
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

def __rsub__(self,y) :
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

def __mul__(self,y) :
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

def __div__(self,y) :
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

def __rdiv__(self,y) :    # y/self
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
  else :
    s = self._basefield;
    q = s._q;
    xt = polynomial(*map(s,unpack(q,x)));
    x = pack(q,map(_x,xt.__pow__(e,self._polynomial)[::-1]));
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
             order=element_order,generator=generates, leastfield=leastfield,
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
      return tuple(self(i) for i in range(*key.indices(self._q)));
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
