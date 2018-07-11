# class rational, implementing Q, the field of rational numbers

from __future__ import division

import sys

from math import log as _mlog, copysign as _mcopysign
from itertools import chain, count

if sys.version_info[0] < 3 :

  def isint(x) :
    """Return True iff an integer"""
    return isinstance(x,(int,long));

  def isrational(x) :
    """Return True iff rational"""
    return isinstance(x,(int,long,rational,xrational));

else :

  xrange = range;

  def isint(x) :
    """Return True iff an integer"""
    return isinstance(x,int);

  def isrational(x) :
    """Return True iff rational"""
    return isinstance(x,(int,rational,xrational));

try :
  int.bit_length;
  bit_length = lambda n : n.bit_length();
except :
  def bit_length(n) :
    n = abs(n);
    b = 0;
    while n :
      try :
        l = int(_mlog(n,2));
        while n >> l : l += 1;
      except OverflowError :
        l = sys.float_info.max_exp-1;
      b += l
      n >>= l;
    return b;

_finf = float('inf');

def sgn(x) :
  """Return the sign of x as an integer: -1, 0, or +1"""
  return -1 if x < 0 else 1 if x > 0 else _nan if x else 0;

def gcd(x,y) :
  """Return the [nonnegative] greatest common divisor of x and y"""
  while y :
    x,y = y, x%y;
  return abs(x);

def root(a,n) :
  """Return the nth root of a, where a and n are positive integers"""
  l = _mlog(a,2)/n;
  if l < 1 : return 1;
  try :
    r = int(round(2**l));
  except :    # too big
    il = int(l)-52;
    fl = l - il;
    r = int(round(2**fl))<<52;
  while True :
    if r**n == a : return r;
    ro = r;
    r = ((n-1)*r + a//r**(n-1))//n;
    if -1 <= ro-r <= 1 :
      return ro if abs(a-ro**n) < abs(a-r**n) else r;

_zits = '0123456789abcdefghijklmnopqrstuvwxyz';

def _parsenum(s,b=10) :
  s = s.lstrip();
  if not s : raise ValueError('empty string');
  p = None;
  n = 0;
  for i,c in enumerate(s) :
    try :
      d = _zits.index(c,0,b);
      n = b*n + d;
    except :
      if c == '.' :
        if p != None : raise ValueError('only one point is allowed');
        p = i;
        continue;
      break;
  else :
    i+=1;
  if not i-(p!=None) : raise ValueError('number must have at least one zit');
  return rational(n)/b**(i-1-p) if p != None else n,s[i:];

def _parsebasenum(s) :
  s = s.lstrip();
  try :
    q = ('inf','nan').index(s[:3]);
    return (_pinf,_nan)[q],s[3:];
  except :
    pass;
  n,s = _parsenum(s);
  s = s.lstrip();
  if s and s[0] == '#' :
    b = n;
    if not (isint(n) and 2<=b<=36) : raise ValueError('base must be between 2 and 36 inclusive');

    n,s = _parsenum(s[1:],b);
  else :
    b = 10;
  q,s = _parseshift(s);
  if q :
    n = n*b**q;
  s = s.lstrip();
  if s and s[0] == '/' :
    d,s = _parsenum(s[1:],b);
    q,s = _parseshift(s);
    if q :
      d = d*b**q;
    n /= rational(d);
  return n,s;

def _parseshift(s) :
  s = s.lstrip();
  try :
    q = 1-2*('<<','>>').index(s[:2]);
  except :
    q = 0;
  if q :
    p,s = _parseint(s[2:]);
    if not isint(p) : raise ValueError('shift amount must be an integer');
  return q and rational(p*q),s;

def _parsesign(s) :
  s = s.lstrip();
  try :
    q = 1-2*('+-').index(s[:1]);
    s = s[1:]
  except :
    q = 1;
  return q,s;

def _parseint(s) :
  q,s = _parsesign(s);
  n,s = _parsenum(s);
  return q*n,s;

def _parsesignednum(s) :
  q,s = _parsesign(s);
  n,s = _parsebasenum(s);
  return q*rational(n),s;

def _parserat(s) :
  s = s.strip().lower();
  a,s = _parsesignednum(s);
  s = s.lstrip();
  if s :
    if s[0] in '*i' :
      if s[0] == '*' :
        s = s[1:].lstrip();
      if s == 'i' :
        return xrational(0,a);
      raise ValueError('real part terminates as if imaginary')
    b,s = _parsesignednum(s);
    if s :
      if s[0] == '*' :
        s = s[1:].lstrip();
      if s == 'i' :
        return xrational(a,b);
    raise ValueError('improper imaginary portion')
  return rational(a);

class rational(object) :
  """Rational number class
Instance variables:
  a or numerator: the numerator, an integer
  b or denominator: the denominator, a positive integer (except -1 for -0)
  Note that gcd(a,b) == 1.
Methods:
  __new__, __init__, __hash__, __repr__, __str__, __bool__, __nonzero__,
  __eq__, __ne__, __lt__, __le__, __ge__, __gt__,
  __pos__, __neg__, __abs__, __invert__, maxnorm,
  __int__, __float__, __round__, __ceil__, __floor__, __trunc__,
  __add__, __radd__, __sub__, __rsub__, __mul__, __rmul__, __div__, __rdiv__,
  __truediv__, __rtruediv__, __floordiv__, __rfloordiv__, __mod__, __rmod__,
  __divmod__, __rdivmod__, __lshift__, __rshift__
  __pow__, __rpow__, log, exp, cf, approximate"""

  def __new__(cls,a=0,b=1,_gcd_=True) :
    """Create a rational number equal to a/b; 0/0 is nan; a/0 is sgn(a)*inf, 0/-1 is -0
If a is a float or rational (and b==1), return the simplest rational whose float is a
If a is a string (and b==1), it is interpreted in liberalized bstr() and/or str() format
If a is iterable (and b==1), its elements, which must be numbers,
are interpreted as the terms of a regular continued fraction
_gcd_ is intended only for internal use: not _gcd_ promises gcd(a,b) = 1"""
    if not isint(a) or not isint(b) :
      if b == 1 :
        if isinstance(a,(rational,xrational)) :
          return a if a.imag else a.real;
        if isinstance(a,str) :
          return _parserat(a);
        try :
          a = iter(a);
          m0,m1,n0,n1 = 0,1,1,0;    # |m0n1-m1n0| == 1 throughout
          for i in a :
            if not isrational(i) :
              try :
                i = rational(i);
              except :
                raise ValueError('cf terms must be rational');
            if not isint(i) and not i.imag and i.real._b == 1 :
              i = int(i);
            m0,m1,n0,n1 = n0,n1,m0+i*n0,m1+i*n1;
          if isint(n0) and isint(n1) :
            a,b = int(n0),int(n1)
            if b < 0 :
              a,b = -a,-b;
          else :
            return n0/n1;
        except TypeError :
          if a.imag :
            return xrational(a);
          elif isinstance(a.real,float) :
            a = a.real;
            if isnan(a) :
              a = b = 0;
            elif isinf(a) :
              a,b = sgn(a),0;
            elif not a :
              a,b = 0,int(_mcopysign(1,a));
            else :
              x = b = abs(a);
              m0,m1,n0,n1 = 0,1,1,0;    # |m0n1-m1n0| == 1 throughout
              for i in xrange(64) :
                ix = x//1;
                fx = x - ix;        
                iix = int(ix);
                m0,m1,n0,n1 = n0,n1,m0+iix*n0,m1+iix*n1;
                if fx == 0 or n0/n1 == b : break;
                x = 1/fx;
                if isinf(x) :    # fx was denormalized
                  c = 1;
                  while True :
                    fx *= 2;
                    x = 1/fx;
                    if not isinf(x) : break;
                    c += 1
                  x = int(1/fx)<<c;
              a,b = sgn(a)*int(n0),int(n1);
          else :
            raise TypeError('arg must be a number or an iterable of cf terms')
      else :
        raise TypeError('numerator and denominator must be integers');
    else :
      if not b :
        a = sgn(a);    # nan, +-inf
      elif not a :
        a,b = 0,sgn(b);
      else :
        if b < 0 : a,b = -a,-b;
        if _gcd_ :
          g = gcd(a,b);
          a = int(a//g);
          b = int(b//g);
    if not a :
      try :
        return _0 if b > 0 else _m0 if b else _nan;
      except :
        pass;    # happens exactly once!
    elif not b :
      try :
        return _minf if a < 0 else _pinf;
      except :
        pass;
    self = super(rational,cls).__new__(cls);
    self._a,self._b = a,b;
    return self;

  def __init__(self,a=0,b=1,_gcd_=True) :
    """Do nothing--all the work has been done by __new__"""
    return;

  def __str__(self) :
    """Return a string showing the rational number as a fraction or integer"""
    return '%d/%d'%(self._a,self._b) if abs(self._b) != 1 else '%s%d'%((self._b<0)*'-',self._a);

  def __repr__(self) :
    """Return a string showing the rational number"""
    return 'rational(%s)'%(self);

  def __hash__(self) :
    """Return a hash for the rational number; if an integer, use that integer's hash"""
    try :
      return hash(self._a) if self._b == 1 else hash(self._a/self._b);
    except :
      return hash(self.cf());

  def __getattr__(self,name) :
    if name in ('a','numerator') :
      return self._a;
    if name in ('b','denominator') :
      return self._b;
    if name == 'real' :
      return self;
    if name == 'imag' :
      return _0;
    raise AttributeError('%s has no attribute %s'%(self.__class__.__name__,name));

  def __lt__(self,other) :
    """Return True iff self < other """
    if self is _nan : return False;
    if not isinstance(other,self.__class__) :
      if isint(other) :
        return self._a < abs(self._b)*other;
      if isinstance(other,float) :
        other = self.__class__(other);
      else :
        return NotImplemented;
    if not other._b :
      return other._a > 0 and (self._b != 0 or self is _minf);
    return self._a*abs(other._b) < abs(self._b)*other._a;

  def __le__(self,other) :
    """Return True iff self <= other"""
    if self is _nan : return False;
    if not isinstance(other,self.__class__) :
      if isint(other) :
        return self._a <= abs(self._b)*other;
      if isinstance(other,float) :
        return self <= self.__class__(other);
      return NotImplemented;
    if not other._b :
      return other._a > 0 or other is self;
    return self._a*abs(other._b) <= abs(self._b)*other._a;

  def __eq__(self,other) :
    """Return True iff self == other"""
    if self is _nan : return False;
    if not isinstance(other,self.__class__) :
      if isint(other) :
        return self._a == abs(self._b)*other;
      if isinstance(other,float) :
        return self == self.__class__(other);
      return NotImplemented;
    return self._a == other._a and abs(self._b) == abs(other._b) and other is not _nan;

  def __ne__(self,other) :
    """Return True iff self != other"""
    if self is _nan : return True;
    if not isinstance(other,self.__class__) :
      if isint(other) :
        return self._a != abs(self._b)*other;
      if isinstance(other,float) :
        return self != self.__class__(other);
      return NotImplemented;
    return self._a != other._a or abs(self._b) != abs(other._b) or other is _nan;

  def __ge__(self,other) :
    if self is _nan : return False;
    """Return True iff self >= other"""
    if not isinstance(other,self.__class__) :
      if isint(other) :
        return self._a >= abs(self._b)*other;
      if isinstance(other,float) :
        return self >= self.__class__(other);
      return NotImplemented;
    if not other._b :
      return other._a < 0 or self == other;
    return self._a*abs(other._b) >= abs(self._b)*other._a;

  def __gt__(self,other) :
    """Return True iff self > other"""
    if not isinstance(other,self.__class__) :
      if isint(other) :
        return self._a > abs(self._b)*other;
      if isinstance(other,float) :
        return self > self.__class__(other);
      else :
        return NotImplemented;
    if not other._b :
      return other._a < 0 and (self._b != 0 or self is _pinf);
    return self._a*abs(other._b) > abs(self._b)*other._a;

  def __bool__(self) :
    """Return True iff self != 0"""
    return self._a != 0 or self._b == 0;

  __nonzero__ = __bool__

  def __pos__(self) :
    """Return self"""
    return self;

  __invert__ = __pos__

  def __neg__(self) :
    """Return -self"""
    return self.__class__(-self._a,self._b if self._a else -self._b,0);

  def __abs__(self) :
    """Return |self|"""
    return self.__class__(-self._a,self._b,0) if self._a < 0 else self or _0;

  maxnorm = __abs__

  def __add__(self,other) :
    """Return the sum of the two numbers"""
    if self is _nan : return _nan;
    if not isinstance(other,self.__class__) :
      if other.imag :
        return xrational(self)+other;
      try :
        return self+self.__class__(other);
      except :
        return other.__class__(self)+other;
    if not other._b :
      return other if other._a and self is not -other else _nan;
    if not self._a :
      return other or (_0 if other._b > 0 or self._b > 0 else _m0);
    return self.__class__(self._a*other._b+other._a*self._b,self._b*other._b);

  __radd__ = __add__

  def __sub__(self,other) :
    """Return the difference of the two numbers"""
    if self is _nan : return _nan;
    if not isinstance(other,self.__class__) :
      try :
        return self-self.__class__(other);
      except :
        return other.__class__(self)-other;
    if not other._b :
      return -other if other._a and self is not other else _nan;
    if not other._a :
      return self or (_0 if other._b < 0 or self._b > 0 else _m0);
    return self.__class__(self._a*other._b-other._a*self._b,self._b*other._b);

  def __rsub__(self,other) :
    """Return the difference of the swapped two numbers"""
    try :
      return self.__class__(other)-self;
    except :
      return other-other.__class__(self);

  def __mul__(self,other) :
    """Return the product of the two numbers"""
    if not isinstance(other,self.__class__) :
      if isint(other) :
        return self.__class__(self._a*other,self._b) if self._a else self if other >= 0 else -self;
      try :
        return self*self.__class__(other);
      except :
        return other.__class__(self)*other;
    if not self._a and not other._b or not other._a and not self._b : return _nan;
    if not self._a :
      return self if other._a >= 0 and other._b > 0 else -self;
    if not other._a :
      return other if self._a > 0 else -other;
    return self.__class__(self._a*other._a,self._b*other._b);

  __rmul__ = __mul__

  def __truediv__(self,other) :
    """Return the quotient of the two numbers"""
    if not isinstance(other,self.__class__) :
      if isint(other) :
        return self.__class__(self._a,other*self._b) if self._b else \
          self if other >= 0 else -self;
      try :
        return self/self.__class__(other);
      except :
        return other.__class__(self)/other;
    a,b = self._a*other._b,self._b*other._a;
    if not a and not b : return _nan;
    if not self._a :
      return self if other._a > 0 else -self;
    if not self._b :
      return self if other._a >= 0 and other._b > 0 else -self;
    return self.__class__(a,b);

  def __rtruediv__(self,other) :
    """Return the inverse quotient of the two numbers"""
    if not isinstance(other,self.__class__) :
      if isint(other) :
        return self.__class__(other*self._b,self._a if self._b or other >= 0 else -self._a)
      try :
        return self.__class__(other)/self;
      except :
        return other/other.__class__(self);
    a,b =self._b*other._a,self._a*other._b;
    if not a and not b : return _nan;
    if not other._a :
      return other if self._a > 0 else -other;
    if not other._b :
      return other if self._a >= 0 and self._b > 0 else -other;
    return self.__class__(a,b);

  __div__ = __truediv__
  __rdiv__ = __rtruediv__

  def __floordiv__(self,other) :
    """Return the floor of the quotient of the two numbers"""
    if not self._b :
      return self/other if other else _nan;
    if not isinstance(other,self.__class__) :
      if isint(other) :
        return self.__class__(self._a//(self._b*other));
      if isinstance(other,complex) :
        return xrational(self)//other;
      try :
        return self//self.__class__(other);
      except :
        return other.__class__(self)//other;
    if not other._b or not other: return _nan;
    return self.__class__((self._a*other._b)//(self._b*other._a));

  def __rfloordiv__(self,other) :
    """Return the floor of the inverse quotient of the two numbers"""
    if not isinstance(other,self.__class__) :
      if isint(other) :
        return self.__class__((self._b*other)//self._a);
      if isinstance(other,complex) :
        return other//xrational(self);
      try :
        return self.__class__(other)//self;
      except :
        return other//other.__class__(self);
    return other//self;

  def __mod__(self,other) :
    """Return the remainder from floordiv"""
    q = self//other;
    return self - q*other if q._b else _0 if q._a else _nan;

  def __rmod__(self,other) :
    """Return the remainder from rfloordiv"""
    return self.__class__(other)%self;

  def __divmod__(self,other) :
    """Return quotient and remainder"""
    q = self//other;
    return (q, self-q*other if q._b else _0 if q._a else _nan);

  def __rdivmod__(self,other) :
    """Return quotient and remainder"""
    return (q, other-q*self if q._b else _0 if q._a else _nan);

  def __pow__(self,other) :
    """Return a number raised to a power; integer powers give exact answer"""
    if self is _nan : return _nan;
    if other.imag :
      try :
        return xrational(self)**other;
      except :
        return exp(other*self.log());
    other = other.real;
    if isinstance(other,float) :
      other = self.__class__(other);
    if isinstance(other,self.__class__) and abs(other._b) == 1 :
      other = other._a;
    if isint(other) :
      if other < 0 :
        return self.__class__(self._b**-other,self._a**-other,0);
      return self.__class__(self._a**other,self._b**other,0);
    if not isinstance(other,self.__class__) :
      raise TypeError('exponent must be a number');
    if not other._b :    # non-finite power
      return _nan if other is _nan \
        else _1 if self == 1 else _pinf if (self > 1) == (other._a > 0) else _0;
    # rational (but not integral) power
    if not self._a :    # zero base
      if other < 0 :
        self = 1/self;
        other = -other;
      return self if other._a&1 else abs(self) if other else _1;
    if not self._b :    # infinite base
      return _pinf if self._a > 0 or not other._a&1 else _minf if other._b&1 else xrational(self)**other;
    if other._a < 0 :
      if self._a < 0 :
        a,b,c = -self._b, -self._a, -other._a;
      else :
        a,b,c = self._b, self._a, -other._a;
    elif other._a :
      a,b,c = self._a, self._b, other._a;
    d = other._b;
    s = 1;    # tentative sign of result
    if a < 0 :
      if not d&1 :
        return xrational(self)**other;    # even root of negative number
      if c&1 :
        s = -1;
      a = -a;
    # result should be s*a**(c/d) / b**(c/d)
    q,r = divmod(c,d);
    if 2*r > d :
      q += 1;
      r -= d;
    ac,bc = s*a**q,b**q;    # to integer power
    if r < 0 : a,b,r = b,a,-r;
    # want (a/b)**(r/d) * ac/bc
    # first see if a and/or b has an integer root
    ra = root(a,d);
    rb = root(b,d);
    pa = ra**d == a;  # a has an exact root?
    pb = rb**d == b;  # b has an exact root?
    if pa and pb :
      return self.__class__(ra**r*ac,rb**r*bc,0);    # exact result
    return _exp(self.__class__(a,b).log()*r/d)*ac/bc;

  def __rpow__(self,other) :
    try :
      return self.__class__(other)**self;
    except :
      return other**other.__class__(self);

  def __lshift__(self,other) :
    """Return the product of self and 2**other, for other an integer"""
    return self.__class__(self._a<<other,self._b) if other >= 0 else self>>-other;

  def __rshift__(self,other) :
    """Return the quotient of self and 2**other, for other an integer"""
    return self.__class__(self._a,self._b<<other) if other >= 0 else self<<-other;

  def __float__(self) :
    """Return a floating point approximation to the number"""
    if not self._b :
      return sgn(self._a)*_finf;
    try :
      return self._a/self._b;
    except OverflowError :
      return sgn(self)*_finf;

  def __int__(self) :
    """Return the integer part of the number"""
    return int(-(-self._a//self._b) if self._a < 0 else self._a//self._b);

  __trunc__ = __int__

  def __floor__(self) :
    """Return the floor of the number"""
    try :
      return int(self._a//self._b);
    except :
      return self;

  def __ceil__(self) :
    """Return the ceil of the number"""
    try :
      return int(-(-self._a//self._b));
    except :
      return self;

  def __round__(self,n=0,base=10) :
    """Return the round of the number"""
    if not isint(n) :
      raise TypeError('n must be an integer');
    if not isint(base) or base < 2 :
      raise ValueError('base must be an integer > 1');
    try :
      if not n : return -int(_half-self) if self._a < 0 else int(_half+self);
      base2absn = base**abs(n);
      return ((self.__class__(int((self/base2absn - _half)*base2absn)) if self._a < 0 else
               self.__class__(int((self/base2absn + _half)*base2absn))) if n < 0 else
              self.__class__(-int(_half - self*base2absn),base2absn) if self._a < 0 else
              self.__class__(int(_half + self*base2absn),base2absn));
    except :
      return self;

  def tonx(self,n,base=10) :
    """Return (0,0) if self == 0; else
Return (t,x) with base**(n-1) <= |t| < base**n and |t-self/base**x| <= 1/2"""
    if not (isint(n) and n > 0) :
      raise ValueError('n must be a positive integer');
    if not isint(base) or base < 2 :
      raise ValueError('base must be an integer > 1');
    if not self :
      return (0,0);
    s = abs(self);
    x = int(s.log(base));
    base = rational(base);
    while base**x > s :
      x -= 1;
    while base**(x+1) <= s :
      x += 1;
    t = int(s*base**(n-x-1)+_half);
    base = int(base);
    if t >= base**n :
      t //= base;
      x += 1;
    return (sgn(self)*t,x+1-n);

  def bstr(self,n=5,base=10) :
    """Return an n-digit string representation of self in the specified base;
if the base is not ten, it is included as a decimal number followed by a number sign;
a following << indicates multiplication by the indicated power of the base;
a following >> indicates division by the indicated power of the base"""
    if not (isint(n) and n > 0) :
      raise ValueError('n must be a positive integer');
    if not (isint(base) and 2 <= base <= 36) :
      raise ValueError('base must be an integer in [2,36]')
    if self._b <= 0 :
      return '-0' if self._b else '-inf' if self._a < 0 else 'inf' if self._a else 'nan';
    if not self : return '+0';
    t,x = self.tonx(n,base);
    t = abs(t);
    s = [];
    while t :
      s.append('0123456789abcdefghijklmnopqrstuvwxyz'[t%base]);
      t //= base;
    s = ''.join(s[::-1]);
    return ('-' if self < 0 else '') + (str(base)+'#' if base != 10 else '') + ( 
      s + '<<' + str(x) if x > 0 else
      '.' + s + '>>' + str(-x-len(s)) if -x > len(s) else
      s[:len(s)+x] + ('.' + s[len(s)+x:] if x else ''));

  def arg(self,ratio=False) :
    """Return 0 if self >= +0, pi or 1/2 if self <= -0 else nan; """
    if not self : self = 1/self;
    return _0 if self._a > 0 else (_half if ratio else pi) if self._a < 0 else _nan;

  def log(self,base=None) :
    """Return the log of the number as a rational"""
    base = self.__class__(base) if base != None else e;
    if not base.real._b or base.imag or base <= 0 or base == 1 : raise ValueError('bad base');
    d = _ln(base);
    return xrational(_ln(-self)/d,pi/d) if self._a < 0 or self._b < 0 else _ln(self)/d;

  def exp(self) :
    """Return exp(self) as a rational"""
    return _exp(self);

  def cf(self) :
    """Return a tuple of the terms of the regular continued fraction for the number"""
    return tuple(self.cfg());

  def cfg(self) :
    """Return a generator of the terms of the regular continued fraction for the number"""
    a,b = self._a,self._b;
    while b :
      q = int(a//b);    # turn long into int if possible
      yield q;
      a,b = b,int(a-q*b);

  def approximate(self,accuracy=None) :
    """If accuracy is unspecified, or self is an integer, return self; else
If self is negative, approximate -self and return the negative; else
If self < 1, approximate 1/self and return the inverse; else
Return x with least denominator such that |(1-x/self)*accuracy| <= 1"""
    if accuracy == None : return self;
    a,b = self._a,self._b;
    if b <= 1 : return self;
    s = sgn(a);    # make sure symmetric over negation
    a *= s;
    if a == 1 : return self;
    v = a < b;
    if v : a,b = b,a;    # make sure symmetric over inversion
    if b*b <= accuracy : return self;
    za,zb = a,b;
    m0,m1,n0,n1 = 0,1,1,0;
    while b :
      q = a//b;
      o0,o1 = m0+q*n0,m1+q*n1;    # fully-included term
      if n1 :
        #if abs((z-self.__class__(o0,o1))/z*accuracy) <= 1 :
        if _checkaccuracy(accuracy,za,zb,o0,o1) :
          n = (q+1)//2;    # min possible term
          x = q;           # max possible term
          while True :
            i = (n+x)//2;
            p0,p1 = m0+i*n0,m1+i*n1;
            #r = self.__class__(p0,p1);
            #if abs((z-r)/z*accuracy) > 1 :
            if not _checkaccuracy(accuracy,za,zb,p0,p1) :
              n = i+1;
            else :
              x = i;
              if x == n :
                return self.__class__(s*p1,p0,0) if v else self.__class__(s*p0,p1,0);
      else :
        r = q + (q*(q+1)*zb*zb < za*za);
        #if abs((z-r)/z*accuracy) <= 1 :
        if _checkaccuracy(accuracy,za,zb,r,1) :
          return self.__class__(s,r,0) if v else self.__class__(s*r);
      m0,m1,n0,n1 = n0,n1,o0,o1;
      a,b = b, a-q*b;
    return self;

class xrational(object) :
  """Complex Rational number class
Instance variables:
  real: the real part, a rational
  imag: the imaginary part, a rational
Methods:
  __new__, __init__, __hash__, __repr__, __str__, __bool__, __nonzero__,
  __eq__, __ne__, __lt__, __le__, __ge__, __gt__,
   __pos__, __neg__, __abs__, __invert__, conjugate, maxnorm,
  __float__, __complex__,
  __add__, __radd__, __sub__, __rsub__, __mul__, __rmul__, __div__, __rdiv__,
  __truediv__, __rtruediv__, __floordiv__, __rfloordiv__, __mod__, __rmod__,
  __divmod__, __rdivmod__, __lshift__, __rshift__
  __pow__, __rpow__, log, exp, arg, approximate"""

  def __new__(cls,real=0,imag=0) :
    """Create a complex number equal to real+imag*i; real and imag are converted to rational
If real is complex or xrational (and imag==0), return the corresponding xrational
If real is a string (and imag==0), return xrational(rational(real))"""
    if imag == 0 :
      if isinstance(real,xrational) : return real;
      if isinstance(real,complex) :
        real,imag = real.real, real.imag;
      if isinstance(real,str) :
        return xrational(rational(real));
    try :
      real = rational(real);
      imag = rational(imag);
      if real.imag or imag.imag : raise TypeError;
    except :
      raise TypeError('args must be convertible to rationals');
    self = super(xrational,cls).__new__(cls);
    self._a,self._b = real,imag;
    return self;

  def __init__(self,real=0,imag=0) :
    """Do nothing--all the work has been done by __new__"""
    return;

  def __str__(self) :
    """Return a string showing the complex rational number"""
    return '%s%s%si'%(self._a,
                      '' if self._b._a < 0 or self._b._b < 0 else '+',
                      self._b) if self._b is not _0 else '%s'%(self._a);

  def __repr__(self) :
    """Return a string showing the rational number"""
    return 'xrational(%s)'%(self);

  def __hash__(self) :
    """Return a hash for the xrational number; if an integer, use that integer's hash"""
    try :
      return hash(complex(self._a,self._b));
    except :
      return hash((self._a,self._b));

  def __getattr__(self,name) :
    if name == 'real' :
      return self._a;
    if name == 'imag' :
      return self._b;
    raise AttributeError('%s has no attribute %s'%(self.__class__.__name__,name));

  def __eq__(self,other) :
    """Return True iff self == other"""
    if not isinstance(other,self.__class__) :
      try :
        other = self.__class__(other);
      except :
        return NotImplemented;
    return self._a == other._a and self._b == other._b;

  def __ne__(self,other) :
    """Return True iff self != other"""
    if not isinstance(other,self.__class__) :
      try :
        other = self.__class__(other);
        if not isinstance(other,self.__class__) : raise NotImplemented;
      except :
        return NotImplemented;
    return self._a != other._a or self._b != other._b;

  def __lt__(self,other) :
    if self._b :
      raise TypeError('no ordering relation is defined for complex numbers');
    return self._a < other;

  def __le__(self,other) :
    if self._b :
      raise TypeError('no ordering relation is defined for complex numbers');
    return self._a <= other;

  def __gt__(self,other) :
    if self._b :
      raise TypeError('no ordering relation is defined for complex numbers');
    return self._a > other;

  def __ge__(self,other) :
    if self._b :
      raise TypeError('no ordering relation is defined for complex numbers');
    return self._a >= other;

  def __bool__(self) :
    """Return True iff self != 0"""
    return bool(self._a) or bool(self._b);

  __nonzero__ = __bool__

  def __pos__(self) :
    """Return self"""
    return self;

  def __neg__(self) :
    """Return -self"""
    return self.__class__(-self._a,-self._b);

  def __invert__(self) :
    """Return complex conjugate of self"""
    return self.__class__(self._a,-self._b);

  conjugate = __invert__

  def __abs__(self) :
    """Return |self|"""
    return (self._a**2+self._b**2)**_half;

  def maxnorm(self) :
    """Return max(|self._a|,|self._b|)"""
    return max(abs(self._a),abs(self._b));

  def __float__(self) :
    """Return a floating point approximation to the number if real"""
    if self._b : raise TypeError('complex');
    return float(self._a);

  def __complex__(self) :
    """Return a floating point [i.e., complex] approximation to the number"""
    return complex(self._a,self._b);

  def __add__(self,other) :
    """Return the sum of the two numbers"""
    if not isinstance(other,self.__class__) :
      try :
        other = self.__class__(other);
      except :
        if isinstance(other,(float,complex)) :
          return complex(self._a+other.real,self._b+other.imag);
        return other.__class__(self) + other;
    return self.__class__(self._a+other._a,self._b+other._b);

  __radd__ = __add__

  def __sub__(self,other) :
    """Return the difference of the two numbers"""
    if not isinstance(other,self.__class__) :
      try :
        other = self.__class__(other);
      except :
        if isinstance(other,(float,complex)) :
          return complex(self._a-other.real,self._b-other.imag);
        return other.__class__(self) - other;
    return self.__class__(self._a-other._a,self._b-other._b);

  def __rsub__(self,other) :
    """Return the difference of the swapped two numbers"""
    try :
      return self.__class__(other)-self;
    except :
      if isinstance(other,(float,complex)) :
        return complex(other.real-self._a,other.imag-self._b);
      return other - other.__class__(self);

  def __mul__(self,other) :
    """Return the product of the two numbers"""
    if not isinstance(other,self.__class__) :
      try :
        other = self.__class__(other);
      except :
        if isinstance(other,(float,complex)) :
          return (complex(self._a*other.real,self._a*other.imag) if not self._b else
                  complex(-self._b*other.imag, self._b*other.real) if not self._a else
                  complex(self._a*other.real-self._b*other.imag,self._a*other.imag+self._b*other.real));
        return other.__class__(self)*other;
    return self.__class__(self._a*other._a-self._b*other._b,self._a*other._b+self._b*other._a);

  __rmul__ = __mul__

  def __div__(self,other) :
    """Return the quotient of the two numbers"""
    if not isinstance(other,self.__class__) :
      try :
        other = self.__class__(other);
      except :
        if isinstance(other,(float,complex)) :
          other = complex(other);
        return other.__class__(self)/other;
    d = other._a**2 + other._b**2;
    return self.__class__((self._a*other._a+self._b*other._b)/d,(self._b*other._a-self._a*other._b)/d);

  def __rdiv__(self,other) :
    """Return the inverse quotient of the two numbers"""
    if not isinstance(other,self.__class__) :
      try :
        other = self.__class__(other);
      except :
        if isinstance(other,(float,complex)) :
          return (complex(other.real/self._a, other.imag/self._a) if not self._b else
                  complex(other.imag/self._b, -other.real/self._b) if not self._a else
                  other*(1/self));
        return other/other.__class__(self);
    return other/self;

  __truediv__ = __div__
  __rtruediv__ = __rdiv__

  if sys.version_info[0] < 3 :

    def __floordiv__(self,other) :
      """Return the floor of the real part of self/other"""
      return self.__class__((self/other)._a.__floor__());

    def __rfloordiv__(self,other) :
      """Return the floor of the real part of other/self"""
      return self.__class__((other/self)._a.__floor__());

    def __mod__(self,other) :
      """Return the remainder from floordiv"""
      return self - self//other*other;

    def __rmod__(self,other) :
      """Return the remainder from rfloordiv"""
      return other - other//self*self;

    def __divmod__(self,other) :
      """Return quotient and remainder"""
      q = self//other;
      return (q, self-q*other);

    def __rdivmod__(self,other) :
      """Return quotient and remainder"""
      q = other//self;
      return (q, other-q*self);

  def __pow__(self,other) :
    """Return a number raised to a power; integer powers give exact answer"""
    other = rational(other);
    if not other.imag :
      other = other.real;
      if not other._b :
        if not other._b : return _nan;
        b = other._a;
        return _1 if b == 1 else _0 if (b<1)==(other>0) else _pinf;
    if isinstance(other,rational) and abs(other._b) == 1 :
      other = other._a;
    if isint(other) :
      if not self : return self._a**other;
      if other < 0 :
        return (1/self)**-other;
      x = self.__class__(_1);
      s = self;
      while other :
        if other&1 : x*=s;
        other >>= 1;
        if not other : break;
        s *= s;
      return x;
    if not self : return _nan if other.imag or other < 0 else _0;
    try :
      return (self.__class__(other)*self.log()).exp();
    except :
      return exp(other*self.log());

  def __rpow__(self,other) :
    try :
      return self.__class__(other)**self;
    except :
      return other**other.__class__(self);

  def __lshift__(self,other) :
    """Return the product of self and 2**other, for other an integer"""
    return self.__class__(self._a<<other,self._b<<other) if other >= 0 else self>>-other;

  def __rshift__(self,other) :
    """Return the quotient of self and 2**other, for other an integer"""
    return self.__class__(self._a>>other,self._b>>other) if other >= 0 else self<<-other;

  def bstr(self,n=5,base=10) :
    """Return a string representation of self, using rational.bstr"""
    return self._a.bstr(n,base) + ('+' if self._b > 0 else '') + \
      self._b.bstr(n,base) + ('i' if base <= 10 else '*i');

  def arg(self,ratio=False) :
    """Return the argument of self; if ratio, as a fraction of 2pi"""
    x,y = self._a,self._b;
    if not x and not y :
      x,y = 1/x,1/y;    # treat +-0 as if +-inf, because why not?
    a = r = None;
    if not y :
      r = rational(1-sgn(x),4)*sgn(y._b);
    elif not x :
      r = rational(sgn(y),4);
    elif abs(x) == abs(y) :
      r = rational(sgn(y)*(2-sgn(x)),8);
    else :
      a = _atan2(y,x);
    if ratio :
      return a/tau if r==None else r;
    else :
      return tau*r if a==None else a;

  def log(self,base=None) :
    """Return the log of the number as an xrational"""
    base = rational(base) if base != None else e;
    if not base.real._b or base.imag or base <= 0 or base == 1 : raise ValueError('bad base');
    if not self : return _pinf if base < 1 else _minf;
    d = _ln(base);
    return self.__class__(_ln(abs(self))/d,self.arg()/d);
    
  def exp(self) :
    """Return exp(self) as an xrational"""
    i = self._b;
    m = _exp(self._a);
    c = _xcos(i);
    s = _xsin(i);
    return self.__class__(c and m*c,s and m*s);
    
  def approximate(self,accuracy=None) :
    return self.__class__(self._a.approximate(accuracy),self._b.approximate(accuracy));

_0=rational(0);
_1=rational(1);
_m0=rational(0,-1);
_pinf=rational(1,0);
_minf=rational(-1,0);
_nan=rational(0,0);
_i=xrational(_0,_1);
_half = rational(1,2);
_hi = xrational(_0,_half);

inf = _pinf;
nan = _nan;

# 327 bits :
e = rational(chain((2,1),chain.from_iterable((2*i,1,1) for i in xrange(1,30))));
log2e = rational((1,2,3,1,6,3,1,1,2,1,1,1,1,3,10,1,1,1,2,1,1,1,1,3,2,3,1,13,7,4,1,1,1,7,2,4,1,1,2,5,14,1,10,1,4,2,18,3,1,4,1,6,2,7,3,3,1,13,3,1,4,4,1,3,1,1,1,1,2,17,3,1,2,32,1,1,1,1,3,1,4,5,1,1,4,1,3,9,8,1,1,7,1,1,1,1,1,1,1,4,5,4,32,1,19,2,1,1,52));   #,43,1,1,7,2,1,3,28))
# 322 bits :
pi = rational((3,7,15,1,292,1,1,1,2,1,3,1,14,2,1,1,2,2,2,2,1,84,2,1,1,15,3,13,1,4,2,6,6,99,1,2,2,6,3,5,1,1,6,8,1,7,1,2,3,7,1,2,1,1,12,1,1,1,3,1,1,8,1,1,2,1,6,1,1,5,2,2,3,1,2,4,4,16,1,161,45,1,22,1,2,2,1,4,1,2,24,1));    #,2,1,3,1,2,1,1));
tau = 2*pi;
hpi = pi/2;
qpi = pi/4;
rootpi = rational((1,1,3,2,1,1,6,1,28,13,1,1,2,18,1,1,1,83,1,4,1,2,4,1,288,1,90,1,12,1,1,7,1,3,1,6,1,2,71,9,3,1,5,36,1,2,2,1,1,1,2,5,9,8,1,7,1,2,2,1,63,1,4,3,1,6,1,1,1,5,1,9,2,5,4,1,2,1,1,2,20,1,1,2,1,10,5,2,1,100));    #,11,1,9,1,2,1,1,1,1));
eulerconstant = rational((0,1,1,2,1,2,1,4,3,13,5,1,1,8,1,2,4,1,1,40,1,11,3,7,1,7,1,1,5,1,49,4,1,65,1,4,7,11,1,399,2,1,3,2,1,2,1,5,3,2,1,10,1,1,1,1,2,1,1,3,1,4,1,1,2,5,1,3,6,2,1,2,1,1,1,2,1,3,16,8,1,1,2,16,6,1,2,2,1,7,2,1,1,1,3,1,2,1,2,13,5,1,1,1,6));    #,1,2,1,1,11,2,5,6));
# 263 bits :
goldenratio = rational(1 for i in xrange(190));  # (1+root5)/2
root2 = rational(min(i,2) for i in xrange(1,105)); # root2**2 > 2 [see froot2]
roothalf = 1/root2;
# 261 bits :
froot2 = root2 - 1;    # required for _atan: froot2 > (1-froot2)/(1+froot2)
if froot2 < (1-froot2)/(1+froot2) : raise ValueError('root2 too small for atan');

_SIGNIFICANCE = 80;   # bits of significance for below functions
MIN_SIGNIFICANCE = 16;    # somewhat arbitrary
MAX_SIGNIFICANCE = 256;   # based on transcendental constants

def set_significance(significance=None) :
  """Set/return number of bits of significance for transcendental functions"""
  global _SIGNIFICANCE
  if not isint(significance) :
    if significance != None :
      raise TypeError('significance must be an integer');
  elif not MIN_SIGNIFICANCE <= significance <= MAX_SIGNIFICANCE :
    raise ValueError('significance must be between %d and %d',
                     MIN_SIGNIFICANCE, MAX_SIGNIFICANCE);
  else :
    _SIGNIFICANCE = significance;
  return _SIGNIFICANCE;

def _checkaccuracy(a,za,zb,ra,rb) :    # assume za,zb,ra,rb all positive
  d = za*rb;
  return abs(a*(d-zb*ra)) <= d;    # abs(z-r)/z*a <= 1

def _isinsignificant(term,total,significance) :
  """Return True if abs(term)<<significance <= abs(total)"""
  return abs(term._a*total._b) <= abs(term._b*total._a)>>significance;

def _exp(x) :
  if not x._b : return _0 if x._a < 0 else x;
  n = x.__round__();
  x -= n;
  en = (e**n).approximate(1<<(_SIGNIFICANCE+8));
  if x <= 0 :
    if x :
      return en/_expp(-x);
    return en;
  return (en*_expp(x));

def _expp(x) :   # 0 < x <= 1/2
  x = x.approximate(1<<(_SIGNIFICANCE+16));
  t = 0;    # compute expm1 to full significance, then add 1 at the end
  s = 1;
  for i in count(1) :
    s *= x/i;
    t += s;
    if _isinsignificant(s,t,_SIGNIFICANCE) : break;
  return 1+t.approximate(1<<(_SIGNIFICANCE+8));

def _xsin(t) :
  """Return sin(t) as a rational"""
  if not t._b : return _nan;
  t %= tau;
  r = 8*t/tau;
  if int(r) == r :
    return (r,roothalf,_1,roothalf,_0,-roothalf,-_1,-roothalf)[int(r)];
  return _sin(t);

def _xcos(t) :
  """Return cos(t) as a rational"""
  if not t._b : return _nan;
  t %= tau;
  r = 8*t/tau;
  if int(r) == r :
    return (_1,roothalf,_0,-roothalf,-_1,-roothalf,_0,roothalf)[int(r)];
  return _sin((t-hpi)%tau-pi);

def _atan2(y,x) :
  if not x/y :
    return hpi*sgn(y);
  a = _atan(y/x);
  return a if x > 0 else a+(sgn(y) or 1)*pi;

def _atan(z) :
  if z < 0 :
    return -_atan(-z);
  if z > 1 :
    return hpi - _atan(1/z);
  if z > froot2 :
    return qpi - _atan((1-z)/(1+z)) if z != -1 else qpi;
  # 0 <= z <= v2-1
  z = z.approximate(1<<(_SIGNIFICANCE+16));
  w = -z*z;
  s = t = z;
  for i in count(3,2) :
    s *= w;
    t += s/i;
    if _isinsignificant(s,z,_SIGNIFICANCE) : break;
  return t.approximate(1<<(_SIGNIFICANCE+8));

def _ln(z) :
  if not z._b : return z;    # nan or inf
  if z <= 1 :
    if z <= 0 :
      if not z : return _minf;
      raise ValueError('math domain error');
    if z < 1 :
      return -_ln(1/z);
    return _0;
  if z == e : return _1
  b = bit_length(int(z)) - 1;
  z >>= b;    # 1 <= z < 2
  if z > root2 :
    z >>= 1;
    b += 1;
  # v2/2 < z <= v2
  return (-_mln1p(1-z) if z < 1 else _mln1p(1-1/z) if z > 1 else 0)+b/log2e;

def _mln1p(x) :    # z = 1-x; -ln z, for v2/2 < z < 1
  x = x.approximate(1<<(_SIGNIFICANCE+16));
  t = s = x;    # 0 < x < 1-v2/2
  for i in count(2) :
    s *= x;
    t += s/i;
    if _isinsignificant(s,x,_SIGNIFICANCE) : break;
  return t.approximate(1<<(_SIGNIFICANCE+8));

def _sin(z) :
  z = (z+pi)%tau - pi;
  if abs(z) > hpi :
    z = sgn(z)*pi - z;
  # -hpi <= z <= hpi
  z /= 27;
  z = z.approximate(1<<(_SIGNIFICANCE+16));
  w = -z*z;
  s = t = z;
  for i in count(3,2) :
    s *= w/(i*(i-1));
    t += s;
    if _isinsignificant(s,z,_SIGNIFICANCE+5) : break;
  for i in xrange(3) :
    t = 3*t - 4*t**3;
  return t.approximate(1<<(_SIGNIFICANCE+8));

# math functions

def exp(x) :
  """Return e**x"""
  return rational(x).exp();

def expm1(x) :
  """Return e**x-1"""
  return exp(x)-1 if x else rational(x);

def log(x,base=e) :
  """Return the logarithm of x for the specified base;
Return the natural logarithm if base is not specified"""
  return xrational(x).log(base) if x.imag else rational(x).log(base);

def log1p(x) :
  """Return the natural logarithm of 1+x"""
  return log(_1+x) if x else rational(x);

def log10(x) :
  """Return the base 10 logarithm of x"""
  return log(x,10);

def log2(x) :
  """Return the base 2 logarithm of x"""
  return log(x,2);

def sin(x) :
  """Return the sine of x (radians)"""
  x = rational(x);
  if not x.real._b or not x.imag._b : return _nan;
  if x.imag :
    ix = _i*x;
    return (((-ix).exp()-ix.exp())*_hi).approximate(1<<(_SIGNIFICANCE+8));
  return _xsin(x.real);

def cos(x) :
  """Return the cosine of x (radians)"""
  x = rational(x);
  if not x.real._b or not x.imag._b : return _nan;
  if x.imag :
    ix = _i*x;
    return (((-ix).exp()+ix.exp())*_half).approximate(1<<(_SIGNIFICANCE+8));
  return _xcos(x.real);

def tan(x) :
  """Return the tangent of x (radians)"""
  x = rational(x);
  if not x.real._b or not x.imag._b : return _nan;
  return sin(x)/cos(x);

def atan2(y,x) :
  """Return the arctangent (in radians) of y/x;
quadrant determined by signs of x and y"""
  x,y = rational(x),rational(y);
  if y.imag or x.imag :
    return atan(y/x) if x else _nan;
  x,y = x.real, y.real;
  return xrational(x,y).arg();

def atan(x) :
  """Return the arctangent (in radians) of x"""
  x = rational(x);
  if x.real is _nan or not x.imag._b :
    return _nan;    #?
  if not x.real._b :
    return _nan if x.imag else hpi if x.real > 0 else -hpi;
  if not x.imag :
    return _atan(x) if x.real else x.real;
  if not x.real and abs(x.imag)==1 :
    return xrational(_0,sgn(x.imag)*_pinf);
  return ((1-_i*x)/(1+_i*x)).log()*_hi;

def acos(x) :
  """Return the arccosine (in radians) of x"""
  return atan2((_1-x*x)**.5,x);

def asin(x) :
  """Return the arcsine (in radians) of x"""
  return atan2(x,(_1-x*x)**.5);

def cosh(x) :
  """Return the hyperbolic cosine of x"""
  x = rational(x);
  if not x.real :
    return cos(x.imag);
  return ((exp(x)+exp(-x))/2).approximate(1<<(_SIGNIFICANCE+8));

def sinh(x) :
  """Return the hyperbolic sine of x"""
  x = rational(x);
  if not x.real and x.imag :
    return xrational(0,sin(x.imag));
  return ((exp(x)-exp(-x))/2).approximate(1<<(_SIGNIFICANCE+8)) if x else x;

def tanh(x) :
  """Return the hyperbolic tangent of x"""
  x = rational(x);
  if x.real is _nan or x.imag is _nan :
    return _nan;
  if not x.real._b and not x.imag :
    return _1*x.a;
  if not x.real and x.imag :
    return xrational(0,tan(x.imag));
  c = cosh(x);
  if not c :
    return sgn(sinh(x).imag)*_pinf;
  return sinh(x)/c;

def atanh(x) :
  """Return the inverse hyperbolic tangent of x"""
  x = rational(x);
  if not x.imag :
    x = x.real;
    if abs(x) == 1 : return sgn(x)*_pinf;
    if not x._b :
      return xrational(0,hpi*x._a) if x._a else _nan;
  if not x.real :
    return xrational(0,atan(x.imag));
  return ((1+x)/(1-x)).log()/2 if x else x;

def acosh(x) :
  """Return the inverse hyperbolic cosine of x"""
  x = rational(x);
  return atanh((_1-_1/(x*x))**.5);

def asinh(x) :
  """Return the inverse hyperbolic sine of x"""
  x = rational(x);
  return (1 if x.imag else sgn(x)) * atanh((_1+_1/(x*x))**-.5) if x else x;

# random math functions

def degrees(x) :
  """Convert from radians to degrees"""
  return x/qpi*45;

def radians(x) :
  """Convert from degrees to radians"""
  return x*qpi/45;

def ldexp(x,i) :
  """Return x*2**i"""
  return rational(x)<<i;

def modf(x) :
  """Return the fractional and integer parts of x,
each with x's sign, as rationals"""
  i,f = rational(abs(x)).__divmod__(1);
  s = copysign(1,x);
  return s*f,s*i;

def pow(x,y) :
  """Return x**y"""
  return rational(x)**y;

def sqrt(x) :
  """Return x**(1/2)"""
  return rational(x)**.5;

def trunc(x) :
  """Return the truncation of x to the nearest integer toward 0; uses __trunc__"""
  return x.__trunc__();

def fsum(iterable) :
  """Return an accurate sum of the values in the iterable"""
  pra = [];    # positive reals
  nra = [];    # negative reals
  pia = [];    # positive imags
  nia = [];    # negative imags
  for i in iterable :
    if i.real :
      if i.real > 0 :
        pra.append(rational(i.real));
      else :
        nra.append(rational(i.real));
    if i.imag :
      if i.imag > 0 :
        pia.append(rational(i.imag));
      else :
        nia.append(rational(i.imag));
  rt = _fsum(pra,nra);
  it = _fsum(pia,nia);
  return xrational(rt,it) if it else rt;

def insert_upright(a,x) :
  """Return where to insert item x in list a, assuming a is sorted lo to hi"""
  lo = 0;
  hi = len(a);
  while lo < hi :
    m = (lo+hi)//2;
    if x < a[m] :
      hi = m;
    else :
      lo = m+1;
  a.insert(lo,x);

def insert_downright(a,x):
  """Return where to insert item x in list a, assuming a is sorted hi to lo"""
  lo = 0;
  hi = len(a);
  while lo < hi :
    m = (lo+hi)//2;
    if x > a[m] :
      hi = m;
    else :
      lo = m+1;
  a.insert(lo,x);

def _fsum(pa,na) :    # pa elements all >0, na elements all <0
  # elements are sorted in increasing absolute value
  pa.sort();
  na.sort(reverse=True);
  while pa and na :
    s = pa.pop()+na.pop();
    if s < 0 :
      insert_downright(na,s);
    elif s :
      insert_upright(pa,s);
  # all remaining elements have same sign
  a = pa or na;
  try :
    s = a.pop();
  except :
    return _0;
  while a :
    if _isinsignificant(a[-1],s,_SIGNIFICANCE+8+bit_length(len(a)-1)) : break;
    s += a.pop();
  return s.approximate(1<<(_SIGNIFICANCE+8));

def frexp(x) :
  """Return (m,p) such that x=m*2**p and 1/2 <= |m| < 1, except
return (x,0) if x is 0 or not finite"""
  x = rational(x);
  if not x._a or not x._b : return (x,0);
  e = int(log2(abs(x))//1) + 1;
  return (x>>e,e);

def fmod(x,y) :
  """Return x%y"""
  return rational(x)%y;

def floor(x) :
  """Return the largest integer not greater than x, or x if not finite"""
  return rational(x)//1;

def ceil(x) :
  """Return the smallest integer not less than x, or x if not finite"""
  return -(rational(-x)//1);

def hypot(x,y) :
  """Return sqrt(|x|**2 + |y|**2)"""
  x,y = rational(x), rational(y);
  return sqrt(x*~x + y*~y);

def isnan(x) :
  """Return True if x is nan, False otherwise"""
  return x != x;

def isinf(x) :
  """Return True if |x| is inf, False otherwise"""
  if x.imag :
    return isinf(max(abs(x.real),abs(x.imag)));
  try :
    return x*2 == x and bool(x);
  except :
    return False;

def isfinite(x) :
  """Return False if |x| is inf or nan, True otherwise"""
  return not isinf(x) and not isnan(x);

def copysign(x,y) :
  """Return |x|*s as a rational, where s is the sign of y;
if either arg has an imaginary component, copy signs componentwise"""
  x = rational(x);
  y = rational(y);
  if isinstance(x,xrational) or isinstance(y,xrational) :
    return xrational(copysign(x.real,y.real),copysign(x.imag,y.imag));
  if x is _nan or y is _nan : return _nan;
  return abs(x)*sgn(y._a or y._b);

def fabs(x) :
  """Return abs(x) as a rational"""
  return abs(rational(x));

def erf(x) :
  """Return the error function at x"""
  if not x : return _0;
  x = rational(x).approximate(1<<(_SIGNIFICANCE+16));
  if x.real is _nan or not x.imag._b : return _nan;    #?
  if not x.imag :
    x = x.real
    if not x._b : return rational(x._a);
    if x*x*log2e > _SIGNIFICANCE+7 :    # erfc(|x|) <= (exp(-x*x)+exp(-2x*x))/2
      return _1*sgn(x);
  return _erf(x);

def _erf(x,a=0) :    # if a, adjust significance for erfc = 1 - erf
  if a : a = max(-_SIGNIFICANCE,(x*x*log2e+log2(x)+log2(rootpi)).__ceil__());
  w = -x*x;
  s = t = x;
  for i in count(1) :
    s *= w/i;
    u = s/(2*i+1);
    t += u;
    if _isinsignificant(u.maxnorm(),t.maxnorm(),a+_SIGNIFICANCE) : break;
  t *= 2/rootpi;
  return t.approximate(1<<(a+_SIGNIFICANCE+8));

def erfc(x) :
  """Return the complementary error function at x"""
  if x.imag :
    return 1-erf(x);
  x = rational(x.real).approximate(1<<(_SIGNIFICANCE+16));
  if x <= 4 :
    if x <= 0 :
      return 1+erf(-x) if x else _1;
    return 1-_erf(x,True);
  if not x._b : return _0 if x._a else _nan;
  v = -x*x;
  w = 2*v;
  s = t = 1;
  for i in count(1) :
    r = (2*i-1)/w ;
    if -r._a >= r._b :    # series began diverging
#      # + (-1)**i/rootpi/2**(2i-1)*(2i)!/i! integral(x,oo) t**-2i exp(-t**2) dt
#      f = lambda t : (x**2-t**2).exp()/(t/x)**(2*i);
#      return (t+((((i&1)-2)*factorial(2*i)//factorial(i)/rootpi)>>(2*i-1))*integral(f,x,inf)*(-x**2).exp()/x**(2*i))*v.exp()/rootpi/x;
      return 1-_erf(x,True);
    s *= r;    # -**i*1*3*5*...(2i-1)/(2x)**(2i)
    t += s;
    if _isinsignificant(s,t,_SIGNIFICANCE) : break;
  t *= v.exp()/rootpi/x;
  return t.approximate(1<<(_SIGNIFICANCE+8));
    
def sinc(x) :
  """Return the sinc function at x, i.e. sin pi*x / pi*x"""
  if not x : return _1;
  x = rational(x);
  if not x.imag and not x.real._b :
    return 1/x.real;
  x *= pi;
  return sin(x)/x;

def lgamma(x) :
  """Return the log of the gamma function at x"""
  x = rational(x);
  if not x.imag :
    if abs(x._b) == 1 :
      return log(factorial(x._a-1)) if x._a > 0 else _pinf ;
    if not x._b : return x;
  if x.real <= 0 :
    z = 1-x;
    return -sinc(z).log()-lgamma(1+z);
  p = 1;
  x = x.approximate(1<<(_SIGNIFICANCE+16));
  while x.real < 32 :    # this increases required intermediate significance
    p *= x;
    x += 1;
  t = x.log() * (x-_half) - x + _half*tau.log();
  u = x;
  w = x*x;
  for i in count(1) :
    s = bernoulli(2*i)/(2*i*(2*i-1))/u;
    t += s;
    if _isinsignificant(s.maxnorm(),t.maxnorm(),_SIGNIFICANCE+8) : break;
    u *= w;
  return (t-p.log()).approximate(1<<(_SIGNIFICANCE+8));

def gamma(x) :    # note gamma(x) = gamma(x+1)/x
  """Return the gamma function at x"""
  x = rational(x);
  if not x.imag :
    x = x.real;
    if abs(x._b) == 1 :
      return rational(factorial(x._a-1)) if x > 0 else _pinf;
  return lgamma(x).exp();    # real if not x.imag

def factorial(x) :
  """Return x!, i.e., gamma(1+x)"""
  if not isint(x) or x < 0:
    n = rational(x);
    if n.imag or n._a != x or n._a < 0: return gamma(1+x);
    x = n._a;
  y = 1;
  for n in xrange(x,1,-1) :
    y *= n;
  return y;

def combinations(n,k) :    # n!/(k!(n-k)!) = n*(n-1)*...(n-k+1)/k!
  """Return the number of combinations of n things taken k at a time"""
  n = int(n);
  k = int(k);
  if not 0 <= k <= n :
    raise ValueError('args must be nonnegative integers with n >= k');
  if k<<1 > n :
    k = n-k;
  a = 1;
  for i in xrange(n,n-k,-1) : a*=i;
  for i in xrange(k,1,-1) : a//=i;
  return a;

def bernoulli(k,pos=False) :
  """Return the kth Bernoulli number; pos determines the sign of bernoulli(1)"""
  k = int(k);
  if k < 0 :
    raise ValueError('k must be nonnegative integer');
  p = int(pos);
  if not 0 <= p <= 1 :
    raise ValueError('pos must be True or False');
  s = _0;
  for i in xrange(k+1) :
    for j in xrange(i+1) :
      s += (1-((j&1)<<1)) * combinations(i,j) * rational((j+p)**k,i+1);
  return s;

def isclose(a,b,rel_tol=rational(1e-9), abs_tol=0) :
  """Return True if a is close in value to b; False otherwise:
a == b or abs(a-b) <= abs_tol or abs(a-b)/max(abs(a),abs(b)) <= rel_tol"""
  if a == b : return True;
  d = abs(a-b);
  return d <= abs_tol or d/max(abs(a),abs(b)) <= rel_tol;

_2_3 = rational(2,3);

def integral(f,a,b,n=256,algorithm='simpson') :
  """Return an approximation to the integral of f from a to b, using n intervals
and specified algorithm ('midpoint','trapezoid',or 'simpson')"""
  if not isint(n) or n <= 0 : raise ValueError('n must be a positive integer');
  a = rational(a);
  b = rational(b);
  d = (b-a)/n;
  if not d or isnan(d) : return d;
  g = f;
  if isinf(d) :
    def f(y) :
      z = 1-abs(y);
      return g(y/z)/z**2 if z else _0;
    a = sgn(a) if isinf(a) else a/(1+abs(a));
    b = sgn(b) if isinf(b) else b/(1+abs(b));
    d = rational(b-a)/n;
  else :
    f = lambda y: rational(g(y));
  if algorithm == 'midpoint' :
    s = fsum(f(a+(i+_half)*d) for i in xrange(n))*d;
  elif algorithm == 'trapezoid' :
    s = fsum(chain((f(a)/2,f(b)/2),(f(a+i*d) for i in xrange(1,n))))*d;
  elif algorithm == 'simpson' :
    if n%2 : raise ValueError('n must be even for simpson');
    s = fsum(chain((f(a)/2,f(b)/2),(f(a+i*d)*(1+i%2) for i in xrange(1,n))))*(_2_3*d)
  else :
    raise ValueError('unrecognized algorithm');
  return s.approximate(1<<(_SIGNIFICANCE+8));
