# class rational, implementing Q, the field of rational numbers,
#   including support for Z, the ring of integers
# class xrational, implementing Q(i), the field of complex rationals,
#   including support for Z(i), the ring of Gaussian integers
# class qrational, implementing the skew field of rational quaternions,
#   including support for the ring of Hurwitz integers
# rational approximations of various constants and functions, including
# numerous math functions for rational, xrational, and sometimes qrational,
#   equivalent to those for float provided by "include math"
# xgcd (extended euclidean algorithm), for various classes,
#   including int, rational, xrational, and qrational

from __future__ import division

import sys

from math import log as _mlog, modf as _mmodf, ldexp as _mldexp, copysign as _mcopysign
from itertools import chain, count
from . conversions import xrange, isint, isstr, gcd, bit_length, lcm, lcma
from . quaternion import quaternion

if sys.version_info[0] < 3 :

  def isrational(x) :
    """Return True iff rational"""
    return isinstance(x,(int,long,rational,xrational));

  _fround = round;
  _round = lambda x : x if isint(x) else int(_fround(x));

else :

  def isrational(x) :
    """Return True iff rational"""
    return isinstance(x,(int,rational,xrational));

  _round = round;

def rint(x) :
  """If x is a rational integer, return x.numerator, else, return x"""
  return x.numerator if isinstance(x,rational) and abs(x.denominator)==1 else x;

def realize(x) :
  """If x has a realize attribute, return x.realize(), else return x"""
  try :
    return x.realize();
  except Exception :
    return x;

_finf = float('inf');

def sgn(x) :
  """Return the sign of x as an integer: -1, 0, or +1"""
  return -1 if x < 0 else 1 if x > 0 else _nan if x else 0;

def root(a,n) :
  """Return the nth root of a, where a and n are positive integers"""
  try :
    l = _mlog(a,2)/n;
  except OverflowError :
    l = 0;
  if l < 1 : return 1;
  lf,li = _mmodf(l);
  li = int(li);
  d = min(li,sys.float_info.mant_dig+1);
  r = _round(_mldexp(2**lf,d))<<(li-d);
  while True :
    if r**n == a : return r;
    ro = r;
    r = ((n-1)*r + a//r**(n-1))//n;
    if -1 <= ro-r <= 1 :
      return ro if abs(a-ro**n) < abs(a-r**n) else r;

_zits = '0123456789abcdefghijklmnopqrstuvwxyz';

def _parsenum(s,b=10,r=False) :
  s = s.lstrip();
  if not s : raise SyntaxError('improper termination');
  p = None;
  n = 0;
  for i,c in enumerate(s) :
    try :
      d = _zits.index(c,0,b);
      n = b*n + d;
    except Exception :
      if c == '.' :
        if p != None : raise SyntaxError('only one point is allowed');
        p = i;
        continue;
      break;
  else :
    i+=1;
  if not i-(p!=None) :
    if not r and p == None and s[0] in 'ijk' : return 1,s;
    raise SyntaxError('number must have at least one zit');
  return rational(n)/b**(i-1-p) if p != None else n,s[i:];

def _parsebasenum(s) :
  s = s.lstrip();
  try :
    q = ('inf','nan').index(s[:3]);
    return (_pinf,_nan)[q],s[3:];
  except Exception :
    pass;
  n,s = _parsenum(s);
  s = s.lstrip();
  if s and s[0] == '#' :
    b = n;
    if not (isint(n) and 2<=b<=36) : raise SyntaxError('base must be between 2 and 36 inclusive');

    n,s = _parsenum(s[1:],b,True);
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
  except Exception :
    q = 0;
  if q :
    p,s = _parseint(s[2:]);
    if not isint(p) : raise SyntaxError('shift amount must be an integer');
  return q and rational(p*q),s;

def _parsesign(s,r=False) :
  q = 1;
  try :
    while s :
      s = s.lstrip();
      q *= 1-2*('+-').index(s[:1]);
      s = s[1:]
      r = False;
  except Exception :
    if r : raise SyntaxError('sign required');
  return q,s;

def _parseint(s) :
  q,s = _parsesign(s);
  n,s = _parsenum(s);
  return q*n,s;

def _parsesignednum(s,r=False) :
  q,s = _parsesign(s,r);
  n,s = _parsebasenum(s);
  return q*rational(n),s;

def _parserat(s) :
  rijk = [_0,_0,_0,_0];
  t = 0;
  s = s.strip().lower();
  r = False;
  while s :
    a,s = _parsesignednum(s,r);
    r = True;    # sign now required
    s = s.lstrip();
    if s and s[0] in '*ijk' :
      if s[0] == '*' :
        s = s[1:].lstrip();
      try :
        x = 'ijk'.index(s[0])+1;
        s = s[1:].lstrip();
      except Exception :
        raise SyntaxError('improper termination');
    else :
      x = 0;
    if t & (1<<x) : raise SyntaxError('duplicate component');
    t |= 1<<x;
    rijk[x] = a;
  return rijk[0] if t<2 else xrational(*rijk[:2]) if t<4 else qrational(*rijk);

class rational(object) :
  """Rational number class
Instance variables (read only):
  a or numerator: the numerator, an integer
  b or denominator: the denominator, a positive integer (except -1 for -0)
  Note that gcd(a,b) == 1.
Methods:
  __new__, __hash__, __repr__, __str__, bstr, __bool__, __nonzero__,
  __eq__, __ne__, __lt__, __le__, __ge__, __gt__,
  __pos__, __neg__, __abs__, __invert__, conjugate, maxnorm, abs2,
  __int__, __float__, __round__, __ceil__, __floor__, __trunc__,
  gaussian, lipschitz, hurwitz,
  __add__, __radd__, __sub__, __rsub__, __mul__, __rmul__, __div__, __rdiv__,
  __truediv__, __rtruediv__, __floordiv__, __rfloordiv__, __mod__, __rmod__,
  __divmod__, __rdivmod__, __lshift__, __rlshift__, __rshift__, __rrshift__,
  __pow__, __rpow__, log, exp, cf, approximate, significate, realize"""

  def __new__(cls,a=0,b=1,_gcd_=True) :
    """Create a rational number equal to a/b; 0/0 is nan; a/0 is sgn(a)*inf, 0/-1 is -0
If a is a float (and b==1), return the simplest rational whose float is a
If a is a rational, or an xrational with a.imag!=0, (and b==1), return a
If a is an xrational with a.imag==0, (and b==1), return a.real
If a is a qrational with a.i==a.j==a.k==0, (and b==1), return a.real
If a is a quaternion, return rational(qrational(a.real,a.i,a.j,a.k))
If a is a string (and b==1), it is interpreted in liberalized bstr() and/or str() format
If a is iterable (and b==1), its elements, which must be numbers,
are interpreted as the terms of a regular continued fraction
_gcd_ is intended only for internal use: not _gcd_ promises gcd(a,b) = 1"""
    if not isint(a) or not isint(b) :
      if b == 1 :
        if isinstance(a,(rational,xrational)) :
          return a if a.imag else a.real;
        if isinstance(a,qrational) :
          return a if a.i or a.j or a.k else a.real;
        if isinstance(a,quaternion) :
          return rational(qrational(a.real,a.i,a.j,a.k));
        if isstr(a) :
          return _parserat(a);
        try :
          c = iter(a);
          try :
            a.__call__;  # polynomial ?
            raise ValueError('callable');
          except AttributeError:
            pass;
          try :
            a.dims;  # matrix ?
            raise ValueError('dimensioned');
          except AttributeError:
            pass;
          m0,m1,n0,n1 = 0,1,1,0;    # |m0n1-m1n0| == 1 throughout
          for i in c :
            if not isrational(i) :
              try :
                i = rational(i);
              except Exception :
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
        except ValueError :
          raise TypeError('iterable must not have additional structure');
        except TypeError :
          if a.imag :
            return xrational(a.real,a.imag);
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
                ix,fx = divmod(x,1);
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
          elif isinstance(a.real,rational) :
            return a.real;
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
      except Exception :
        pass;    # happens exactly once for each of (+0,-0,nan)!
    elif not b :
      try :
        return _minf if a < 0 else _pinf;
      except Exception :
        pass;    # happens exactly once for each of (+inf,-inf)!
    self = super(rational,cls).__new__(cls);
    self._a,self._b = a,b;
    return self;

  def __reduce__(self) :
    # return tuple for pickling rational"""
    return (rational,(self._a,self._b));

  def __str__(self) :
    """Return a string showing the rational number as a fraction or integer"""
    return '%d/%d'%(self._a,self._b) if abs(self._b) != 1 else '%s%d'%((self._b<0)*'-',self._a);

  def __repr__(self) :
    """Return a string showing the rational number"""
    return "rational('%s')"%(self);

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
    if not self : return '0';
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

  def __hash__(self) :
    """Return a hash for the rational number; if convertible to float, use that hash"""
    try :
      return hash(self._a) if self._b == 1 else hash(self._a/self._b);
    except Exception :
      return hash((self.cf if self._b else self.__float__)());

  @property
  def real(self) :
    """the real part"""
    return self;

  @property
  def imag(self) :
    """the imaginary part"""
    return _0;

  @property
  def a(self) :
    """the numerator"""
    return self._a;

  @property
  def b(self) :
    """the denominator"""
    return self._b;

  @property
  def numerator(self) :
    """the numerator"""
    return self._a;

  @property
  def denominator(self) :
    """the denominator"""
    return self._b;

  def __lt__(self,other) :
    """Return True iff self < other """
    if self is _nan : return False;
    if not isinstance(other,type(self)) :
      if isint(other) :
        return self._a < abs(self._b)*other;
      if isinstance(other,float) :
        other = type(self)(other);
      else :
        return NotImplemented;
    if not other._b :
      return other._a > 0 and (self._b != 0 or self is _minf);
    return self._a*abs(other._b) < abs(self._b)*other._a;

  def __le__(self,other) :
    """Return True iff self <= other"""
    if self is _nan : return False;
    if not isinstance(other,type(self)) :
      if isint(other) :
        return self._a <= abs(self._b)*other;
      if isinstance(other,float) :
        return self <= type(self)(other);
      return NotImplemented;
    if not other._b :
      return other._a > 0 or other is self;
    return self._a*abs(other._b) <= abs(self._b)*other._a;

  def __eq__(self,other) :
    """Return True iff self == other"""
    if self is _nan : return False;
    if not isinstance(other,type(self)) :
      if isint(other) :
        return self._a == abs(self._b)*other;
      if isinstance(other,float) :
        return self == type(self)(other);
      if isinstance(other,complex) :
        return not other.imag and self == type(self)(other);
      if isinstance(other,quaternion) :
        return not other.i and not other.j and not other.k and self == type(self)(other);
      return NotImplemented;
    return self._a == other._a and abs(self._b) == abs(other._b) and other is not _nan;

  def __ne__(self,other) :
    """Return True iff self != other"""
    if self is _nan : return True;
    if not isinstance(other,type(self)) :
      if isint(other) :
        return self._a != abs(self._b)*other;
      if isinstance(other,float) :
        return self != type(self)(other);
      if isinstance(other,complex) :
        return other.imag or self != type(self)(other.real);
      if isinstance(other,quaternion) :
        return other.i or other.j or other.k or self != type(self)(other.real);
      return NotImplemented;
    return self._a != other._a or abs(self._b) != abs(other._b) or other is _nan;

  def __ge__(self,other) :
    if self is _nan : return False;
    """Return True iff self >= other"""
    if not isinstance(other,type(self)) :
      if isint(other) :
        return self._a >= abs(self._b)*other;
      if isinstance(other,float) :
        return self >= type(self)(other);
      return NotImplemented;
    if not other._b :
      return other._a < 0 or self == other;
    return self._a*abs(other._b) >= abs(self._b)*other._a;

  def __gt__(self,other) :
    """Return True iff self > other"""
    if not isinstance(other,type(self)) :
      if isint(other) :
        return self._a > abs(self._b)*other;
      if isinstance(other,float) :
        return self > type(self)(other);
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
  conjugate = __invert__

  def __neg__(self) :
    """Return -self"""
    return type(self)(-self._a,self._b if self._a else -self._b,0);

  def __abs__(self) :
    """Return |self|"""
    return type(self)(-self._a,self._b,0) if self._a < 0 else self or _0;

  maxnorm = __abs__

  def abs2(self) :
    """Return self*self"""
    return self*self;

  def __add__(self,other) :
    """Return the sum of the two numbers"""
    if self is _nan : return _nan;
    if not isinstance(other,type(self)) :
      try :
        return type(self)(other).__radd__(self);
      except Exception :
        return NotImplemented;
    if not other._b :
      return other if other._a and self is not -other else _nan;
    if not self._a :
      return other or (_0 if other._b > 0 or self._b > 0 else _m0);
    return type(self)(self._a*other._b+other._a*self._b,self._b*other._b);

  __radd__ = __add__

  def __sub__(self,other) :
    """Return the difference of the two numbers"""
    if self is _nan : return _nan;
    if not isinstance(other,type(self)) :
      try :
        return type(self)(other).__rsub__(self);
      except Exception :
        return NotImplemented;
    if not other._b :
      return -other if other._a and self is not other else _nan;
    if not other._a :
      return self or (_0 if other._b < 0 or self._b > 0 else _m0);
    return type(self)(self._a*other._b-other._a*self._b,self._b*other._b);

  def __rsub__(self,other) :
    """Return the difference of the swapped two numbers"""
    try :
      return type(self)(other)-self;
    except Exception :
      return NotImplemented;

  def __mul__(self,other) :
    """Return the product of the two numbers"""
    if not isinstance(other,type(self)) :
      if isint(other) :
        return type(self)(self._a*other,self._b) if self._a else self if other >= 0 else -self;
      try :
        return type(self)(other).__rmul__(self);
      except Exception :
        return NotImplemented;
    if not self._a and not other._b or not other._a and not self._b : return _nan;
    if not self._a :
      return self if other._a >= 0 and other._b > 0 else -self;
    if not other._a :
      return other if self._a > 0 else -other;
    return type(self)(self._a*other._a,self._b*other._b);

  __rmul__ = __mul__

  def __truediv__(self,other) :
    """Return the quotient of the two numbers"""
    if not isinstance(other,type(self)) :
      if isint(other) :
        return type(self)(self._a,other*self._b) if self._b else \
          self if other >= 0 else -self;
      try :
        return type(self)(other).__rtruediv__(self);
      except Exception :
        return NotImplemented;
    a,b = self._a*other._b,self._b*other._a;
    if not a and not b : return _nan;
    if not self._a :
      return self if other._a > 0 else -self;
    if not self._b :
      return self if other._a >= 0 and other._b > 0 else -self;
    return type(self)(a,b);

  def __rtruediv__(self,other) :
    """Return the inverse quotient of the two numbers"""
    if not isinstance(other,type(self)) :
      if isint(other) :
        return type(self)(other*self._b,self._a if self._b or other >= 0 else -self._a,_gcd_=abs(other)!=1)
      try :
        return type(self)(other)/self;
      except Exception :
        return NotImplemented;
    a,b =self._b*other._a,self._a*other._b;
    if not a and not b : return _nan;
    if not other._a :
      return other if self._a > 0 else -other;
    if not other._b :
      return other if self._a >= 0 and self._b > 0 else -other;
    return type(self)(a,b);

  __div__ = __truediv__
  __rdiv__ = __rtruediv__

  def __floordiv__(self,other) :
    """Return the floor of the quotient of the two numbers"""
    if not self._b :
      return self/other if other else _nan;
    if not isinstance(other,type(self)) :
      if isint(other) :
        return type(self)(self._a//(self._b*other));
      try :
        return type(self)(other).__rfloordiv__(self);
      except Exception :
        return NotImplemented;
    if not other._b or not other: return _nan;
    return type(self)((self._a*other._b)//(self._b*other._a));

  def __rfloordiv__(self,other) :
    """Return the floor of the inverse quotient of the two numbers"""
    if not isinstance(other,type(self)) :
      if isint(other) :
        return type(self)((self._b*other)//self._a);
      try :
        return type(self)(other)//self;
      except Exception :
        return NotImplemented;
    return other//self;

  def __mod__(self,other) :
    """Return the remainder from floordiv"""
    q = self//other;
    return self-q*other;

  def __rmod__(self,other) :
    """Return the remainder from rfloordiv"""
    return type(self)(other)%self;

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
    if self is _nan : return _nan;
    try :
      other = type(self)(other);
    except Exception :
      return NotImplemented;
    if not other.real is other :
      return other.__rpow__(self);
    if abs(other._b) == 1 :
      other = other._a;
    if isint(other) :
      if other < 0 :
        return type(self)(self._b**-other,self._a**-other,0);
      return type(self)(self._a**other,self._b**other,0);
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
      return type(self)(ra**r*ac,rb**r*bc,0);    # exact result
    return _exp(type(self)(a,b).log()*r/d)*ac/bc;

  def __rpow__(self,other) :
    try :
      other = type(self)(other);
    except Exception :
      return NotImplemented;
    return other**self;

  def __lshift__(self,other) :
    """Return the product of self and 2**other, for other an integer"""
    return type(self)(self._a<<other,self._b) if other > 0 else self>>-other if other else self;

  def __rlshift__(self,other) :
    if self._b != 1 or not isint(other):
      return NotImplemented;
    return other>>-self._a if self._a < 0 else other<<self._a;

  def __rshift__(self,other) :
    """Return the quotient of self and 2**other, for other an integer"""
    return type(self)(self._a,self._b<<other) if other > 0 else self<<-other if other else self;

  def __rrshift__(self,other) :
    if self._b != 1 or not isint(other):
      return NotImplemented;
    return other<<-self._a if self._a < 0 else other>>self._a;

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
    except Exception :
      return self;

  def __ceil__(self) :
    """Return the ceil of the number"""
    try :
      return int(-(-self._a//self._b));
    except Exception :
      return self;

  def __round__(self,n=None,base=10) :
    """Return the round of the number"""
    if not isint(n or 0) :
      raise TypeError('n must be an integer');
    if not isint(base) or base < 2 :
      raise ValueError('base must be an integer > 1');
    try :
      if not n :
        v = -int(_half-self) if self._a < 0 else int(_half+self);
        return type(self)(v) if isint(n) else v;
      base2absn = base**abs(n);
      return ((type(self)(int((self/base2absn - _half)*base2absn)) if self._a < 0 else
               type(self)(int((self/base2absn + _half)*base2absn))) if n < 0 else
              type(self)(-int(_half - self*base2absn),base2absn) if self._a < 0 else
              type(self)(int(_half + self*base2absn),base2absn));
    except Exception :
      return self;

  def gaussian(self) :
    """Return the integer nearest self, round toward 0"""
    return type(self)(
      -(((-self._a<<1)+self._b-1)//(self._b<<1)) if self._a < 0 else
      ((self._a<<1)+self._b-1)//(self._b<<1)) if self else _0;

  hurwitz = lipschitz = gaussian

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

  def arg(self,ratio=False) :
    """Return 0 if self >= +0, pi or 1/2 if self <= -0 else nan; """
    if not self : self = 1/self;
    return _0 if self._a > 0 else (_half if ratio else pi) if self._a < 0 else _nan;

  def log(self,base=None) :
    """Return the log of the number as a rational"""
    base = type(self)(base) if base != None else e;
    if base is not base.real or not base._b or base <= 0 or base == 1 :
      raise ValueError('bad base');
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
    if not b and a != 1 : raise ValueError('no cf for nan nor -inf');
    while b :
      q,r = divmod(a,b);
      yield int(q);    # long->int if possible
      a,b = b,int(r);  # long->int if possible

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
        #if abs((z-type(self)(o0,o1))/z*accuracy) <= 1 :
        if _checkaccuracy(accuracy,za,zb,o0,o1) :
          n = (q+1)//2;    # min possible term
          x = q;           # max possible term
          while True :
            i = (n+x)//2;
            p0,p1 = m0+i*n0,m1+i*n1;
            #r = type(self)(p0,p1);
            #if abs((z-r)/z*accuracy) > 1 :
            if not _checkaccuracy(accuracy,za,zb,p0,p1) :
              n = i+1;
            else :
              x = i;
              if x == n :
                return type(self)(s*p1,p0,0) if v else type(self)(s*p0,p1,0);
      else :
        r = q + (q*(q+1)*zb*zb < za*za);
        #if abs((z-r)/z*accuracy) <= 1 :
        if _checkaccuracy(accuracy,za,zb,r,1) :
          return type(self)(s,r,0) if v else type(self)(s*r);
      m0,m1,n0,n1 = n0,n1,o0,o1;
      a,b = b, a-q*b;
    return self;

  def significate(self,extrabits=0) :
    """Return an approximation of self with set_significance()+extrabits precision"""
    return self.approximate(1<<max(0,_SIGNIFICANCE+extrabits));

  def realize(self) :
    """Return self as an int or float"""
    return self._a if abs(self._b) == 1 else self.__float__();

def _xrat(a,b,c,d) :
  """Return xrational given numerator and denominator of real and of imag"""
  return xrational(rational(a,b),rational(c,d));

class xrational(object) :
  """Complex Rational number class
Instance variables (read only):
  real: the real part, a rational
  imag: the imaginary part, a rational
  denominator: the lcm of the denominators of real and imag
  numerator: denominator*self
Methods:
  __new__, __hash__, __repr__, __str__, bstr, __bool__, __nonzero__,
  __eq__, __ne__, __lt__, __le__, __ge__, __gt__,
   __pos__, __neg__, __abs__, __invert__, conjugate, maxnorm, abs2,
  __int__, __float__, __complex__, __trunc__, __round__,
  gaussian, lipschitz, hurwitz,
  __add__, __radd__, __sub__, __rsub__, __mul__, __rmul__, __div__, __rdiv__,
  __truediv__, __rtruediv__, __floordiv__, __rfloordiv__, __mod__, __rmod__,
  __divmod__, __rdivmod__, __lshift__, __rshift__,
  __pow__, __rpow__, log, exp, arg, approximate, significate, realize"""

  def __new__(cls,real=0,imag=0) :
    """Create a complex number equal to real+imag*i; real and imag are converted to rational
If real is complex or xrational (and imag==0), return the corresponding xrational
If real is qrational (and imag==0), return real unless real.j and real.k are 0,
  in which case return xrational(real.real, real.i)
If real is a string (and imag==0), return xrational(rational(real))"""
    if imag == 0 :
      if isinstance(real,xrational) : return real;
      if isinstance(real,qrational) :
        if real.j or real.k : return real;
        real,imag = real.real, real.i;
      if isinstance(real,complex) :
        real,imag = real.real, real.imag;
      if isstr(real) or isinstance(real,quaternion) :
        return xrational(rational(real));
    try :
      real = rational(real);
      imag = rational(imag);
      if real.imag or imag.imag : raise TypeError;
    except Exception :
      raise TypeError('args must be convertible to rationals');
    self = super(xrational,cls).__new__(cls);
    self._a,self._b = real,imag;
    return self;

  def __reduce__(self) :
    """Return tuple for pickling xrational"""
    return (_xrat,(self._a._a,self._a._b,self._b._a,self._b._b));

  def __str__(self) :
    """Return a string showing the complex rational number"""
    return '%s%s%si'%(
      '' if self._a is _0 else self._a,
      '' if self._a is _0 or self._b._a < 0 or self._b._b < 0 else '+',
      self._b) if self._b is not _0 else '%s'%(self._a);

  def __repr__(self) :
    """Return a string showing the complex rational number"""
    return "xrational('%s')"%(self);

  def bstr(self,n=5,base=10) :
    """Return a string representation of self, using rational.bstr"""
    return self._a.bstr(n,base) + \
      ('+' if self._b is _0 or self._b._a > 0 else '') + \
      self._b.bstr(n,base) + ('i' if base <= 16 else '*i');

  def __hash__(self) :
    """Return a hash for the xrational number; if convertible to complex, use that hash"""
    try :
      return hash(complex(self._a,self._b));
    except Exception :
      return hash((self._a,self._b));

  @property
  def real(self) :
    """the real part"""
    return self._a;

  @property
  def imag(self) :
    """the imaginary part"""
    return self._b;

  @property
  def denominator(self) :
    """the lcm of real and imag denominators"""
    return lcm(self._a._b,self._b._b);

  @property
  def numerator(self) :
    """self * self.denominator"""
    return self*self.denominator;

  def __eq__(self,other) :
    """Return True iff self == other"""
    if isstr(other) :
      return False;
    try :
      other = type(self)(other);
      return self._a == other._a and self._b == other._b;
    except Exception :
      return NotImplemented;

  def __ne__(self,other) :
    """Return True iff self != other"""
    if isstr(other) :
      return True;
    try :
      other = type(self)(other);
      return self._a != other._a or self._b != other._b;
    except Exception :
      return NotImplemented;

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
    return type(self)(-self._a,-self._b);

  def __invert__(self) :
    """Return complex conjugate of self"""
    return type(self)(self._a,-self._b);

  conjugate = __invert__

  def __abs__(self) :
    """Return |self|"""
    return (self._a*self._a+self._b*self._b)**_half;

  def maxnorm(self) :
    """Return max(|self._a|,|self._b|)"""
    return max(abs(self._a),abs(self._b));

  def abs2(self) :
    """Return |self|**2"""
    return self._a*self._a+self._b*self._b;

  def __int__(self) :
    """Return the integer part of the number if real"""
    if self._b : raise TypeError('complex');
    return int(self._a);

  __trunc__ = __int__

  def __float__(self) :
    """Return a floating point approximation to the number if real"""
    if self._b : raise TypeError('complex');
    return float(self._a);

  def __complex__(self) :
    """Return a floating point [i.e., complex] approximation to the number"""
    return complex(self._a,self._b);

  def __add__(self,other) :
    """Return the sum of the two numbers"""
    if not isinstance(other,type(self)) :
      try :
        return type(self)(other).__radd__(self);
      except Exception :
        return NotImplemented;
    return type(self)(self._a+other._a,self._b+other._b);

  __radd__ = __add__

  def __sub__(self,other) :
    """Return the difference of the two numbers"""
    if not isinstance(other,type(self)) :
      try :
        return type(self)(other).__rsub__(self);
      except Exception :
        return NotImplemented;
    return type(self)(self._a-other._a,self._b-other._b);

  def __rsub__(self,other) :
    """Return the difference of the swapped two numbers"""
    try :
      return type(self)(other)-self;
    except Exception :
      return NotImplemented;

  def __mul__(self,other) :
    """Return the product of the two numbers"""
    if not isinstance(other,type(self)) :
      try :
       return type(self)(other).__rmul__(self);
      except Exception :
        return NotImplemented;
    return type(self)(self._a*other._a-self._b*other._b,self._a*other._b+self._b*other._a);

  __rmul__ = __mul__

  def __div__(self,other) :
    """Return the quotient of the two numbers"""
    try :
      other = rational(other);
      if other is other.real :
        return type(self)(self._a/other,self._b/other);
      if not isinstance(other,type(self)) :
        return NotImplemented;
    except Exception :
      return NotImplemented;
    d = other._a*other._a + other._b*other._b;
    return type(self)((self._a*other._a+self._b*other._b)/d,(self._b*other._a-self._a*other._b)/d);

  def __rdiv__(self,other) :
    """Return the inverse quotient of the two numbers"""
    try :
      other = rational(other);
      if other is other.real :
        a = other/(self._a*self._a + self._b*self._b);
        return type(self)(self._a*a,-self._b*a);
    except Exception :
      return NotImplemented;
    return other/self;

  __truediv__ = __div__
  __rtruediv__ = __rdiv__

  def __floordiv__(self,other) :
    """Return Gaussian or Hurwitz integer nearest to self/other"""
    return (self/other).hurwitz();

  def __rfloordiv__(self,other) :
    """Return Gaussian or Hurwitz integer nearest to other/self"""
    return (other/self).hurwitz();

  def __mod__(self,other) :
    """Return the remainder from floordiv"""
    return self-self//other*other;

  def __rmod__(self,other) :
    """Return the remainder from rfloordiv"""
    return other-other//self*self;

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
    try :
      other = rational(other);
    except Exception :
      return NotImplemented;
    if other is other.real :
      if not other : return _1;
      if not other._b :    # nan or +-inf
        if self.imag or self.real < 0 or other is _nan: return _nan;
        a = self.real;
        return _1 if a == 1 else _0 if (a<1)==(other>0) else _pinf;
      if other._b == 1 :
        other = other._a;
    if isint(other) :
      if not self : return _0**other;
      if other < 0 :
        return (1/self)**-other;
      x = type(self)(_1);
      while other :
        if other&1 : x*=self;
        other >>= 1;
        if not other : break;
        self *= self;
      return x;
    if not self : return _nan if other != other.real or other < 0 else _0;
    p = (self.log()*other).exp();
    a = p.approximate(1<<MIN_SIGNIFICANCE);
    return a if isclose(a,p,rational(1,16<<_SIGNIFICANCE)) else p;

  def __rpow__(self,other) :
    """Return a power of a number; integer powers give exact answer"""
    try :
      other = type(self)(other);
    except Exception :
      return NontImplemented;
    return other**self;

  def __lshift__(self,other) :
    """Return the product of self and 2**other, for other an integer"""
    return type(self)(self._a<<other,self._b<<other) if other > 0 else self>>-other if other else self;

  def __rshift__(self,other) :
    """Return the quotient of self and 2**other, for other an integer"""
    return type(self)(self._a>>other,self._b>>other) if other > 0 else self<<-other if other else self;

  def __round__(self,n=0,base=10) :
    """Return result of separately rounding real and imaginary parts"""
    return type(self)(self._a.__round__(n,base),self._b.__round__(n,base));

  def gaussian(self) :
    """Return Gaussian integer nearest to self"""
    return type(self)(self._a.gaussian(),self._b.gaussian());

  hurwitz = lipschitz = gaussian

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
    if base is not base.real or not base._b or base <= 0 or base == 1 :
      raise ValueError('bad base');
    if not self : return _pinf if base < 1 else _minf;
    d = _ln(base);
    return type(self)(_ln(abs(self))/d,self.arg()/d);
    
  def exp(self) :
    """Return exp(self) as an xrational"""
    i = self._b;
    m = _exp(self._a);
    c = _xcos(i);
    s = _xsin(i);
    return type(self)(c and m*c,s and m*s);
    
  def approximate(self,accuracy=None) :
    """Return result of applying rational.approximate to real and imaginary parts"""
    return type(self)(self._a.approximate(accuracy),self._b.approximate(accuracy));

  def significate(self,extrabits=0) :
    """Return result of applying rational.significate to real and imaginary parts"""
    return type(self)(self._a.significate(extrabits),self._b.significate(extrabits));

  def realize(self) :
    """Return self as an int, float, or complex"""
    return self._a.realize() if not self._b else self.__complex__();

def _qrat(a,b,c,d,e,f,g,h) :
  """Return qrational given numerator and denominator of real and of i,j,k"""
  return qrational(rational(a,b),rational(c,d),rational(e,f),rational(g,h));

class qrational(object):
  """Quaternion class
Instance variables (read only):
   real or r or scalar or s: the real (scalar) part, a rational
   vector or v: the vector part, a tuple of rationals
   i,j,k: the respective components of the vector part, each a rational
   imag: the imaginary part, but only if j and k components are zero
   sv or rv: (s,i,j,k), a tuple of rationals
   denominator: the lcm of the denominators of sv
   numerator: denominator*self
Methods:
  __new__, __hash__, __repr__, __str__, bstr, __bool__, __nonzero__,
  __eq__, __ne__, __lt__, __le__, __ge__, __gt__,
  __pos__, __neg__, __abs__, __invert__, conjugate, versor, maxnorm, abs2,
  __int__, __float__, __complex__, __trunc__, __round__,
  gaussian, lipschitz, hurwitz,
  __add__, __radd__, __sub__, __rsub__, __mul__, __rmul__, __div__, __rdiv__,
  __truediv__, __rtruediv__, __floordiv__, __rfloordiv__, __mod__, __rmod__,
  __divmod__, __rdivmod__, __lshift__, __rshift__,
  __pow__, __rpow__, log, exp, approximate, significate, realize"""

  def __new__(cls,*args) :
    """Create a quaternion, internally a tuple of 4 rationals
If no arg, return the zero quaternion
If a single arg,
  if a qrational, it is returned
  if a string, it is interpreted in liberalized bstr() and/or str() format,
    and the resulting quaternion is returned
  otherwise, the single arg is replaced by its .real and .imag attributes
Now, the args must be real, and are converted to rationals
If two args, the quaternion args[0] + i*args[1] is returned
If three args, the vector quaternion i*args[0] + j*args[1] + k*args[2] is returned
If four args, the quaternion args[0] + i*args[1] + j*args[2] + k*args[3] is returned"""
    self = super(qrational,cls).__new__(cls);
    if not args : args = (_0,);
    if len(args) == 1 :
      if isinstance(args[0],qrational) :
        return args[0];
      if isstr(args[0]) or isinstance(args[0],quaternion) :
        return qrational(rational(args[0]));
      args = (args[0].real,args[0].imag);
    for a in args :
      if isinstance(a,qrational) and (a.i or a.j or a.k) or a.imag :
        raise TypeError('arguments must be real')
    if len(args) == 2 :
      self.__v = (rational(args[0]),rational(args[1]),_0,_0);
    elif len(args) == 3 :
      self.__v = (_0,rational(args[0]),rational(args[1]),rational(args[2]));
    elif len(args) == 4 :
      self.__v = (rational(args[0]),rational(args[1]),rational(args[2]),rational(args[3]));
    else :
      raise TypeError('too many arguments');
    return self;

  def __reduce__(self) :
    """Return tuple for pickling qrational"""
    return (_qrat,(self.__v[0]._a,self.__v[0]._b,self.__v[1]._a,self.__v[1]._b,
                   self.__v[2]._a,self.__v[2]._b,self.__v[3]._a,self.__v[3]._b));

  def __str__(self) :
    """Return a string showing the rational quaternion"""
    return '%s%s%si%s%sj%s%sk'%(
      '' if self.__v[0] is _0 else self.__v[0],
      '' if self.__v[0] is _0 or self.__v[1]._a < 0 or self.__v[1]._b < 0 else '+',
      self.__v[1],
      '' if self.__v[2]._a < 0 or self.__v[2]._b < 0 else '+',
      self.__v[2],
      '' if self.__v[3]._a < 0 or self.__v[3]._b < 0 else '+',
      self.__v[3]
      ) if self.__v[1] is not _0 or self.__v[2] is not _0 or self.__v[3] is not _0 else '%s'%(self.__v[0]);

  def __repr__(self) :
    """Return a string showing the rational quaternion"""
    return "qrational('%s')"%(self);

  def bstr(self,n=5,base=10) :
    """Return a string representation of self, using rational.bstr"""
    return self.__v[0].bstr(n,base) + \
      ('+' if self.__v[1] is _0 or self.__v[1]._a > 0 else '') + \
      self.__v[1].bstr(n,base) + ('i' if base <= 16 else '*i') + \
      ('+' if self.__v[2] is _0 or self.__v[2]._a > 0 else '') + \
      self.__v[2].bstr(n,base) + ('j' if base <= 16 else '*j') + \
      ('+' if self.__v[3] is _0 or self.__v[3]._a > 0 else '') + \
      self.__v[3].bstr(n,base) + ('k' if base <= 16 else '*k');

  def __hash__(self) :
    """Return a hash for the quaternion; if convertible to complex, use that hash"""
    if not any(self.__v[2:]) :    # real or complex
      try :
        return hash(complex(*self.__v[0:2])) if self.__v[1] else hash(self.__v[0]);
      except Exception :
        pass;
    return hash(tuple(self.__v));

  @property
  def real(self) :
    """the real part"""
    return self.__v[0];

  @property
  def imag(self) :
    """the imaginary part when j and k components are zero"""
    if self.__v[2] or self.__v[3] : raise AttributeError('not complex');
    return self.__v[1];

  @property
  def rv(self) :
    """the quaternion as a tuple (r,i,j,k)"""
    return self.__v;

  @property
  def sv(self) :
    """the quaternion as a tuple (s,i,j,k)"""
    return self.__v;

  @property
  def scalar(self) :
    """the scalar part"""
    return self.__v[0];

  @property
  def vector(self) :
    """the vector part as a tuple (i,j,k)"""
    return self.__v[1:];

  @property
  def r(self) :
    """the real part"""
    return self.__v[0];

  @property
  def s(self) :
    """the scalar part"""
    return self.__v[0];

  @property
  def i(self) :
    """the i part"""
    return self.__v[1];

  @property
  def j(self) :
    """the j part"""
    return self.__v[2];

  @property
  def k(self) :
    """the k part"""
    return self.__v[3];

  @property
  def v(self) :
    """the vector part as a tuple (i,j,k)"""
    return self.__v[1:];

  @property
  def denominator(self) :
    """the lcm of the component's denominators"""
    return lcma(map(lambda x:x._b, self.__v));

  @property
  def numerator(self) :
    """self * self.denominator"""
    return self*self.denominator;

  def __bool__(self) :
    return any(self.__v);

  __nonzero__ = __bool__

  def __eq__(self,other) :
    if isstr(other) :
      return False;
    try :
      return self.__v == type(self)(other).__v;
    except Exception :
      return NotImplemented;

  def __ne__(self,other) :
    if isstr(other) :
      return True;
    try :
      return self.__v != type(self)(other).__v;
    except Exception :
      return NotImplemented;

  def __lt__(self,other) :
    if any(self.__v[1:]) :
      raise TypeError('no ordering relation is defined for quaternions');
    return self.__v[0] < other;

  def __le__(self,other) :
    if any(self.__v[1:]) :
      raise TypeError('no ordering relation is defined for quaternions');
    return self.__v[0] <= other;

  def __gt__(self,other) :
    if any(self.__v[1:]) :
      raise TypeError('no ordering relation is defined for quaternions');
    return self.__v[0] > other;

  def __ge__(self,other) :
    if any(self.__v[1:]) :
      raise TypeError('no ordering relation is defined for quaternions');
    return self.__v[0] >= other;

  def __pos__(self) :
    """Return self"""
    return self;

  def __neg__(self) :
    """Return -self"""
    return type(self)(-self.__v[0],-self.__v[1],-self.__v[2],-self.__v[3]);

  def __invert__(self) :
    """Return conjugate of self"""
    return type(self)(self.__v[0],-self.__v[1],-self.__v[2],-self.__v[3]);

  conjugate = __invert__

  def __abs__(self) :
    """Return |self|"""
    return (self.__v[0]*self.__v[0]+self.__v[1]*self.__v[1]+
            self.__v[2]*self.__v[2]+self.__v[3]*self.__v[3])**.5;

  def maxnorm(self) :
    """Return max absolute value of components of self"""
    return max(abs(a) for a in self.__v);

  def abs2(self) :
    """Return |self|**2"""
    return (self.__v[0]*self.__v[0]+self.__v[1]*self.__v[1]+
            self.__v[2]*self.__v[2]+self.__v[3]*self.__v[3]);    

  def versor(self) :
    """Return self/|self|, or 1 if zero"""
    a = abs(self);
    return type(self)(*(x/a for x in self.__v) if a else (1,));

  def __int__(self) :
    """Return the integer part of the number if real"""
    if any(self.__v[1:]) : raise TypeError('not real');
    return int(self.__v[0]);

  __trunc__ = __int__

  def __float__(self) :
    """Return a floating point approximation to the number if real"""
    if any(self.__v[1:]) : raise TypeError('not real');
    return float(self.__v[0]);

  def __complex__(self) :
    """Return a floating point [i.e., complex] approximation to the number if complex"""
    if any(self.__v[2:]) : raise TypeError('not complex');
    return complex(*self.__v[:2]);

  def __add__(self,other) :
    """Return the sum of the two numbers"""
    try :
      other = type(self)(other);
    except Exception :
      return NotImplemented;
    return type(self)(*(x+y for x,y in zip(self.__v,other.__v)));

  __radd__ = __add__;

  __iadd__ = __add__;

  def __sub__(self,other) :
    """Return the difference of the two numbers"""
    try :
      other = type(self)(other);
    except Exception :
      return NotImplemented;
    return type(self)(*(x-y for x,y in zip(self.__v,other.__v)));

  __isub__ = __sub__;
 
  def __rsub__(self,other) :
    """Return the difference of the swapped two numbers"""
    try :
      other = type(self)(other);
    except Exception :
      return NotImplemented;
    return type(self)(*(x-y for x,y in zip(other.__v,self.__v)));

  def __mul__(self,other) :
    """Return the product of the two numbers"""
    try :
      other = rational(other);
      if other is other.real :
        return type(self)(*(v*other for v in self.__v));
    except Exception :
      return NotImplemented;
    other = type(self)(other);
    return type(self)(
      self.__v[0]*other.__v[0]-self.__v[1]*other.__v[1]-self.__v[2]*other.__v[2]-self.__v[3]*other.__v[3],
      self.__v[0]*other.__v[1]+self.__v[1]*other.__v[0]+self.__v[2]*other.__v[3]-self.__v[3]*other.__v[2],
      self.__v[0]*other.__v[2]+self.__v[2]*other.__v[0]+self.__v[3]*other.__v[1]-self.__v[1]*other.__v[3],
      self.__v[0]*other.__v[3]+self.__v[3]*other.__v[0]+self.__v[1]*other.__v[2]-self.__v[2]*other.__v[1]);

  __imul__ = __mul__;

  def __rmul__(self,other) :
    """Return the swapped product of the two numbers"""    
    try :
      other = rational(other);
      if other is other.real :
        return type(self)(*(other*v for v in self.__v));
    except Exception :
      return NotImplemented;
    other = type(self)(other);
    return type(self)(
      other.__v[0]*self.__v[0]-other.__v[1]*self.__v[1]-other.__v[2]*self.__v[2]-other.__v[3]*self.__v[3],
      other.__v[0]*self.__v[1]+other.__v[1]*self.__v[0]+other.__v[2]*self.__v[3]-other.__v[3]*self.__v[2],
        other.__v[0]*self.__v[2]+other.__v[2]*self.__v[0]+other.__v[3]*self.__v[1]-other.__v[1]*self.__v[3],
        other.__v[0]*self.__v[3]+other.__v[3]*self.__v[0]+other.__v[1]*self.__v[2]-other.__v[2]*self.__v[1]);

  def cross(self,other) :
    """Return the cross product of two vectors as a qrational"""
    if self.real or not isinstance(other,type(self)) or other.real:
      return TypeError('args must be vectors');
    return type(self)(_0,self.__v[2]*other.__v[3]-self.__v[3]*other.__v[2],
                             self.__v[3]*other.__v[1]-self.__v[1]*other.__v[3],
                             self.__v[1]*other.__v[2]-self.__v[2]*other.__v[1]);

  def dot(self,other) :
    """Return the dot product of two vectors as a rational"""
    if self.real or not isinstance(other,type(self)) or other.real:
      return TypeError('args must be vectors');
    return self.__v[1]*other.__v[1]+self.__v[2]*other.__v[2]+self.__v[3]*other.__v[3];

  # danger: a*b**-1 != b**-1*a ?
  def __truediv__(self,other) :
    """Return the quotient of the two numbers"""
    try :
      other = rational(other);
      if other is other.real :
        return type(self)(*(v/other for v in self.__v));
    except Exception :
      return NotImplemented;
    return self.__mul__(other.__pow__(-1));

  def __rtruediv__(self,other) :
    """Return the swapped quotient of the two numbers"""
    try :
      other = rational(other);
      if other is other.real :
        a = other/(self.__v[0]*self.__v[0] + self.__v[1]*self.__v[1] +
                   self.__v[2]*self.__v[2] + self.__v[3]*self.__v[3]);
        return type(self)(self.__v[0]*a,-self.__v[1]*a,-self.__v[2]*a,-self.__v[3]*a);
    except Exception :
      return NotImplemented;
    return type(self)(other).__truediv__(self);

  __itruediv__ = __truediv__

  __div__ = __truediv__
  __rdiv__ = __rtruediv__
  __idiv__ = __itruediv__

  def __floordiv__(self,other) :
    """Return Hurwitz integer nearest to self/other"""
    return (self/other).hurwitz();

  def __rfloordiv__(self,other) :
    """Return Hurwitz integer nearest to other/self"""
    return (other/self).hurwitz();

  def __mod__(self,other) :
    """Return the remainder from floordiv"""
    return self-self//other*other;

  def __rmod__(self,other) :
    """Return the remainder from rfloordiv"""
    return other-other//self*self;

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
    try :
      other = rational(other);
    except Exception :
      return NotImplemented;
    if other is other.real :
      if not self :      # special case zero
        return type(self)(_0**other);
      if abs(other._b) == 1 :    # integer power
        r = other._a;
        if not any(self.__v[1:]) :        # real
          return type(self)(self.__v[0]**r);
        if r < 0 :
          a = self.__v[0]*self.__v[0] + self.__v[1]*self.__v[1] + \
              self.__v[2]*self.__v[2] + self.__v[3]*self.__v[3];
          q = type(self)(self.__v[0]/a, -self.__v[1]/a, -self.__v[2]/a, -self.__v[3]/a);
          r = -r;
        else :
          q = self;
        if r==1 : return q;
        result = type(self)(_1,_0,_0,_0);
        while r :
          if r&1 : result *= q;
          r >>= 1;        
          if not r : break;
          q *= q;
        return result;
    p = (self.log()*other).exp();    # a**x = exp(log(a)*x)
    a = p.approximate(1<<MIN_SIGNIFICANCE);
    return a if isclose(a,p,rational(1,16<<_SIGNIFICANCE)) else p;

  __ipow__ = __pow__

  def __rpow__(self,other) :
    """Return a power of a number; integer powers give exact answer"""
    try:
      other = type(self)(other);
    except Exception :
      return NotImplemented;
    return other.__pow__(self);

  def __lshift__(self,other) :
    """Return the product of self and 2**other, for other an integer"""
    return type(self)(*(a<<other for a in self.__v)) if other > 0 else self>>-other if other else self;

  def __rshift__(self,other) :
    """Return the quotient of self and 2**other, for other an integer"""
    return type(self)(*(a>>other for a in self.__v)) if other > 0 else self<<-other if other else self;

  def __round__(self,n=0,base=10) :
    """Return result of separately rounding all parts"""
    return type(self)(*(a.__round__(n,base) for a in self.__v));

  def lipschitz(self) :
    """Return nearest Lipschitz integer to self"""
    return type(self)(*(a.gaussian() for a in self.__v));

  gaussian = lipschitz

  def hurwitz(self) :
    """Return nearest Hurwitz integer to self"""
    x = self.lipschitz();
    y = type(self)(
      *(a if a._b==2 else
        rational(-((-a._a//a._b<<1)|1) if a._a < 0 else (a._a//a._b<<1)|1,
                 2, False)
        for a in self.__v));
    return y if (self-x).abs2() > (self-y).abs2() else x;

  def exp(self) :
    """Return exp(self)"""
    ea = exp(self.__v[0]);
    av = sqrt(self.__v[1]*self.__v[1]+
              self.__v[2]*self.__v[2]+
              self.__v[3]*self.__v[3]);
    s = ea*sin(av)/av if av else 1;
    return type(self)(ea*cos(av),s*self.__v[1],s*self.__v[2],s*self.__v[3]);

  def log(self,base=None) :
    """Return the log of self to the given base (default e)"""
    a = abs(self);
    av = self.__v[1]*self.__v[1]+self.__v[2]*self.__v[2]+self.__v[3]*self.__v[3];
    if not av :
      if self.real < 0 :
        return type(self)(xrational(self).log(base));
      else :
        return type(self)(a.log(base));
    av = sqrt(av);
    ac = (acos(self.__v[0]/a)/av)/log(base or e);
    return type(self)(a.log(base),ac*self.__v[1],ac*self.__v[2],ac*self.__v[3]);
    
  def approximate(self,accuracy=None) :
    """Return result of applying rational.approximate to each component of self"""
    return type(self)(*(a.approximate(accuracy) for a in self.__v));

  def significate(self,extrabits=0) :
    """Return result of applying rational.significate to each component of self"""
    return type(self)(*(a.significate(extrabits) for a in self.__v));

  def realize(self) :
    """Return self as an int, float, complex, or quaternion"""
    return self.__v[0].realize() if not any(self.__v[1:]) else \
      complex(*self.__v[:2]) if not any(self.__v[2:]) else \
      quaternion(*map(rational.realize,self.__v));

_0=rational(0);
_1=rational(1);
_m0=rational(0,-1);
_pinf=rational(1,0);
_minf=rational(-1,0);
_nan=rational(0,0);
_i=xrational(_0,_1);
_half = rational(1,2);
_mhalf = rational(-1,2);
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
    raise ValueError('significance must be between %d and %d'%(
                     MIN_SIGNIFICANCE, MAX_SIGNIFICANCE));
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
  w = (-z*z).approximate(1<<(_SIGNIFICANCE+16));
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
  w = (-z*z).approximate(1<<(_SIGNIFICANCE+16));
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
  return rational(x).log(base);

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
  r = x.real;
  i = x.imag;
  if not r._b or not i._b : return _nan;
  return xrational(_xsin(r)*cosh(i),_xcos(r)*sinh(i)).approximate(1<<(_SIGNIFICANCE+8)) if i else _xsin(r);

def cos(x) :
  """Return the cosine of x (radians)"""
  x = rational(x);
  r = x.real;
  i = x.imag;
  if not r._b or not i._b : return _nan;
  return xrational(_xcos(r)*cosh(i),-_xsin(r)*sinh(i)).approximate(1<<(_SIGNIFICANCE+8)) if i else _xcos(r);

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
    a = atan(y/x) if x else _nan;
    return a - copysign(pi,a.real) if (x.real and x.real < 0 or 
                                       y.real and (a.real < 0) != (y.real < 0)) else a;
  return xrational(x.real,y.real).arg();

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
  return atan2((_1-x*x)**_half,x);

def asin(x) :
  """Return the arcsine (in radians) of x"""
  return atan2(x,(_1-x*x)**_half);

def cosh(x) :
  """Return the hyperbolic cosine of x"""
  x = rational(x);
  r = x.real;
  i = x.imag;
  if i :
    return cos(xrational(i,-r)) if r else cos(i);
  y = exp(r);
  return ((y+1/y)/2).approximate(1<<(_SIGNIFICANCE+8));

def sinh(x) :
  """Return the hyperbolic sine of x"""
  x = rational(x);
  r = x.real;
  i = x.imag;
  if i :
    if r :
      y = sin(xrational(i,-r));
      return xrational(-y.imag,y.real);
    return xrational(0,sin(i));
  if x :
    y = exp(x);
    return ((y-1/y)/2).approximate(1<<(_SIGNIFICANCE+8));
  return x;

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
  return _i*acos(x) if x.imag or x<1 else atanh((_1-_1/(x*x))**_half);

def asinh(x) :
  """Return the inverse hyperbolic sine of x"""
  x = rational(x);
  return -_i*asin(_i*x) if x.imag else sgn(x)*atanh((_1+_1/(x*x))**_mhalf) if x else x;

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

_pow = pow;

def pow(x,y,z=None) :
  """Return x**y if z==None else use built-in pow(x,y,z)"""
  if z == None :
    try :
      return rational(x)**y;
    except Exception :
      pass;
  return _pow(x,y,z);

def sqrt(x) :
  """Return x**(1/2)"""
  return rational(x)**_half;

def trunc(x) :
  """Return the truncation of x to the nearest integer toward 0; uses __trunc__"""
  return x.__trunc__();

def fsum(iterable) :
  """Return an accurate sum of the values in the iterable"""
  pra = [];    # positive reals
  nra = [];    # negative reals
  pia = [];    # positive imags or is
  nia = [];    # negative imags or is
  pja = [];    # positive js
  nja = [];    # negative js
  pka = [];    # positive ks
  nka = [];    # negative ks
  for i in iterable :
    if i.real :
      if i.real > 0 :
        pra.append(rational(i.real));
      elif i.real :
        nra.append(rational(i.real));
    if isinstance(i,qrational) :
      if i.i > 0 :
        pia.append(i.i);
      elif i.i :
        nia.append(i.i);
      if i.j > 0 :
        pja.append(i.j);
      elif i.j :
        nja.append(i.j);
      if i.k > 0 :
        pka.append(i.k);
      elif i.k :
        nka.append(i.k);
    elif i.imag :
      if i.imag > 0 :
        pia.append(rational(i.imag));
      else :
        nia.append(rational(i.imag));
  rt = _fsum(pra,nra);
  it = _fsum(pia,nia);
  jt = _fsum(pja,nja);
  kt = _fsum(pka,nka);
  return qrational(rt,it,jt,kt) if jt or kt else xrational(rt,it) if it else rt;

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
  except Exception :
    return _0;
  while a :
    t = _SIGNIFICANCE+8+bit_length(len(a)-1);
    if _isinsignificant(a[-1],s,t) : break;
    s = (s + a.pop()).approximate(1<<t);
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
  """Return the largest integer not greater than x, or x if not finite;
but if x is not real but complex, return the nearest Gaussian integer;
but if x is not complex but quaternion, return the nearest Hurwitz integer"""
  return rational(x)//1;

def ceil(x) :
  """Return the smallest integer not less than x, or x if not finite;
  but if x is not real, return -floor(-x)"""
  return -(rational(-x)//1);

def hypot(*x) :
  """Return sqrt of sum of squares of absolute values"""
  return sqrt(sum(map(lambda x: rational(x).abs2(),x)));

def dist(p,q) :
  """Return Euclidean distance between points p and q"""
  return hypot(*(rational(x)-rational(y) for x,y in zip(p,q)));

def isnan(x) :
  """Return True if x is nan, False otherwise"""
  return x != x;

def isinf(x) :
  """Return True if |x| is inf, False otherwise"""
  if x.imag :
    return isinf(max(abs(x.real),abs(x.imag)));
  try :
    return x*2 == x and bool(x);
  except Exception :
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

#550 bits: (for _erf used to compute erfc)
_rootpi = rational((1,1,3,2,1,1,6,1,28,13,1,1,2,18,1,1,1,83,1,4,1,2,4,1,288,1,90,1,12,1,1,7,1,3,1,6,1,2,71,9,3,1,5,36,1,2,2,1,1,1,2,5,9,8,1,7,1,2,2,1,63,1,4,3,1,6,1,1,1,5,1,9,2,5,4,1,2,1,1,2,20,1,1,2,1,10,5,2,1,100,11,1,9,1,2,1,1,1,1,3,2,2,3,1,2,7,1,7,2,2,2,11,1,1,2,9,1,9,2,1,1,3,1,1,1,2,1,3,3,1,7,2,1,4,12,5,3,2,1,1,2,2,3,5,2,49,1,1,3,1,3,1,23,1,5,1,2,1,4,1,8,1,1,2,1,1,49,1)); #,16,2,1,3,1,4,25,1,1,1,13,1,19,23,1,13,1,2,1,1,4,4,1,1,1,20,2,4,2,6,5,4,3,7,1,2,25,16));
_twoslashrootpi = 2/_rootpi;

def _erf(x,a=0) :    # if a, adjust significance for erfc = 1 - erf
  if a : a = max(-_SIGNIFICANCE,(x*x*log2e+log2(x)+log2(rootpi)).__ceil__());
  w = (-x*x).approximate(1<<(a+_SIGNIFICANCE+16));
  s = t = x;
  for i in count(1) :
    s *= w/i;
    u = s/(2*i+1);
    t += u;
    if _isinsignificant(u.maxnorm(),t.maxnorm(),a+_SIGNIFICANCE) : break;
  t *= _twoslashrootpi;
  return t.approximate(1<<(a+_SIGNIFICANCE+8));

def erfc(x) :
  """Return the complementary error function at x"""
  if x.imag :
    return 1-erf(x);
  x = rational(x.real).approximate(1<<(_SIGNIFICANCE+16));
  if x <= 0 :
    return 1+erf(-x) if x else _1;
  if x*x*log2e < _SIGNIFICANCE+_half :
    return 1-_erf(x,True);    # series diverges before reaching significance
  if not x._b : return _0 if x._a else _nan;
  v = (-x*x).approximate(1<<(_SIGNIFICANCE+16));
  w = 2*v;
  s = t = 1;
  for i in count(1) :
    r = (2*i-1)/w ;
    if -r._a >= r._b :    # series began diverging
#      # + (-1)**i/rootpi/2**(2i-1)*(2i)!/i! integral(x,oo) t**-2i exp(-t**2) dt
#      f = lambda t : (x**2-t**2).exp()/(t/x)**(2*i);
#      return (t+((((i&1)-2)*factorial(2*i)//factorial(i)/rootpi)>>(2*i-1))*integral(f,x,inf)*(-x**2).exp()/x**(2*i))*v.exp()/rootpi/x;
      return 1-_erf(x,True);    # series diverged before reaching significance
    s *= r;    # -**i*1*3*5*...(2i-1)/2**i/x**(2i)
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

def lgamma(x,base=e) :
  """Return the log of the gamma function at x for the specified base"""
  x = rational(x);
  base = rational(base);
  if base.imag or not base._b or base <= 0 or base == 1 :
    raise ValueError('bad base');
  if not x.imag :
    if abs(x._b) == 1 :
      if x._a <= MAX_SIGNIFICANCE :
        return log(factorial(x._a-1),base) if x._a > 0 else _nan;
    elif not x._b :
      return (_pinf if base > 1 else _minf) if x > 0 else _nan;
  if x.real < 1 :
    z = 1-x;
    return -sinc(z).log(base)-lgamma(1+z,base);
  p = 1;
  x = x.approximate(1<<(_SIGNIFICANCE+16));
  while x.real < 1<<5 :    # this increases required intermediate significance
    p *= x;
    x += 1;
  t = x.log() * (x-_half) - x + _half*tau.log();
  u = x;
  w = (x*x).approximate(1<<(_SIGNIFICANCE+16));
  for i in count(2,2) :
    s = bernoulli(i)/(i*(i-1))/u;
    t += s;
    if _isinsignificant(s.maxnorm(),t.maxnorm(),_SIGNIFICANCE+8) : break;
    u *= w;
  return (t-log(p)).approximate(1<<(_SIGNIFICANCE+8))/log(base);

def gamma(x) :    # note gamma(x) = gamma(x+1)/x
  """Return the gamma function at x"""
  x = rational(x);
  if not x.imag :
    x = x.real;
    if abs(x._b) == 1 :
      return rational(factorial(x._a-1)) if x > 0 else _nan;
  return rational(lgamma(x).exp());    # real if not x.imag

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

def digamma(x,base=e) :    # for base=e, digamma(x+1) = digamma(x) + 1/x
  """Return the digamma function at x"""
  # -eulerconstant+(x-1)sum(n=0,inf) 1/((n+1)(n+x)); x not 0,-1,-2,...
  # ln x - 1/(2*x) - sum(n=1,N) B[2*n]/(2*n*x**(2*n)) - (-1)**N*2/x**(2*N) *
  #                 integral(0,inf) t**(2*N+1)/((t*t+z*z)(exp(2*pi*t)-1)) dt
  # digamma(1-x) - digamma(x) = pi/tan(pi*x)
  x = rational(x);
  base = rational(base);
  if base.imag or not base._b or base <= 0 or base == 1 :
    raise ValueError('bad base');
  if not x.imag :
    if abs(x._b) <= 1 :
      if x._a <= 0 or not x._b : return _nan;
      return (harmonic(x._a-1) - eulerconstant)/log(base);
    elif x._a > 0 and x._b == 2 :
      return (2*oddharmonic(x._a-1) - 2/log2e - eulerconstant)/log(base);
  if x.real < _half :
    x = 1-x;
    s = pi/tan(pi*x);
  else :
    s = 0;
  while x.real < 1<<5 :    # this increases required intermediate significance
    s -= 1/x; # dg(x) = dg(x+1)-1/x
    x += 1;
  u = w = (x*x).approximate(1<<(_SIGNIFICANCE+16));
  for i in count(2,2) :
    t = bernoulli(i)/(i*u);
    s -= t;
    if _isinsignificant(t.maxnorm(),s.maxnorm(),_SIGNIFICANCE+8) : break;
    u *= w;
  return (x.log()-_half/x+s).approximate(1<<(_SIGNIFICANCE+8))/log(base);

def harmonic(n) :
  """Return the nth harmonic number sum(k=1,floor(n)) 1/k"""
  n = int(n);
  if n<0 : raise ValueError('arg must be nonnegtive integer');
  s = 0;
  for i in range(1,n+1) :
    s += rational(1,i);
  return s;

def oddharmonic(n) :
  """Return sum(k=0,ceil(floor(n)/2)) 1/(2k+1) = harmonic(n)-harmonic(n/2)/2"""
  n = int(n);
  if n<0 : raise ValueError('arg must be nonnegative integer');
  s = 0;
  for i in range(1,n+1,2) :
    s += rational(1,i);
  return s;

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
  d = a-b;
  if isinstance(d,(xrational,qrational)) :    # avoid expensive xrational abs
    d = d.abs2();
    return d <= abs_tol**2 or \
           d/max(rational(a).abs2(),rational(b).abs2()) <= rel_tol**2;
  d = abs(d);
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

def xgcd(a,b) :
  """Return g,c,d where g=ca+db is the gcd of a and b"""
  c,d,e,f = 1,0,0,1;
  while b :
    q,r= divmod(a,b);
    a,c,d,b,e,f = b,e,f,r,c-q*e,d-q*f;
  if not a : return (0,0,0);
  if isinstance(a,(xrational,qrational)) :
    if a.real :
      if isinstance(a,qrational) and \
          abs(a.sv[0])==abs(a.sv[1])==abs(a.sv[2])==abs(a.sv[3]) :
        q = qrational(_half if a.sv[0] > 0 else _mhalf,
                      _mhalf if a.sv[1] > 0 else _half,
                      _mhalf if a.sv[2] > 0 else _half,
                      _mhalf if a.sv[3] > 0 else _half);
      else :
        q = sgn(a.real);
    elif isinstance(a,xrational) :
      q = xrational(0,-sgn(a.imag));
    elif a.i :
      q = qrational(0,-sgn(a.i));
    elif a.j :
      q = qrational(0,-sgn(a.j),0);
    else :
      q = qrational(0,0,-sgn(a.k));
    return (rational(q*a),rational(q*c),rational(q*d));
  return (-a,-c,-d) if a.real < 0 else (a,c,d);
