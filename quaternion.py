# quaternion class

from __future__ import division

# Note -1 has uncountably many square roots, we choose i

__all__ = ['quaternion']

import sys

VERSION2 = int(sys.version.split('.')[0]) < 3;
INTTYPE = (int,long,) if VERSION2 else int;
REALTYPE = (int,long,float,) if VERSION2 else (int,float,);
COMPLEXTYPE = (int,long,float,complex) if VERSION2 else (int,float,complex);
STRINGTYPE = (str,unicode) if VERSION2 else str

import math    # exp, log, cos, sin, acos

import re

QRE = re.compile(r'((?:[+-]?)(?:inf|nan|\d*\.?\d*(?:e\d+)?))');

import warnings

warnings.filterwarnings('ignore','',FutureWarning,__name__);

class ParameterError(Exception):
  pass

def isreal(a) :
  return isinstance(a,REALTYPE);

def iscomplex(a) :
  return isinstance(a,COMPLEXTYPE);

def isstring(a) :
  return isinstance(a,STRINGTYPE);

class quaternion(object) :
  """quaternion class
+ - * / ** abs have their normal meaning
  note that multiplication is not commutative
~q is the conjugate of q: ~quaternion(a,b,c,d) == quaternion(a,-b,-c,-d)
q.s, q.r, q.real, q.scalar are each the scalar (real) part of q
q.v, q.vector are each the vector part of q as a tuple
q.i, q.j, q.k are the respective components of the vector part of q
  note that quaternion(-a).log() == quaternion(math.log(a),math.pi) for a>0"""

  def __new__(cls,*args) :
    """Create a quaternion:
quaternion(a) is the real number a
quaternion(a,b) is the complex number a+bi
quaternion(a,b,c) is the vector ai+bj+ck
quaternion(a,b,c,d) is the quaternion a+bi+cj+dk
quaternion(string) is the quaternion represented by that string"""
    self = super(quaternion,cls).__new__(cls);
    if not args : args = (0,);
    if len(args) == 1 :
      if isinstance(args[0],quaternion) :
        return args[0];
      if isstring(args[0]) :        # parse string
        try :
          n = QRE.split(args[0].strip().lower());
          t = -1;
          v = [0,0,0,0];
          if n[0] :
            if n[0] in 'ijk' :
              n = ['']+n;
            else :
              raise ValueError;    # crud before number
          else :
            n = n[1:]
          for i in range(0,len(n),2) :
            x = ('','i','j','k').index(n[i+1]);
            if x <= t :
              raise ValueError;    # duplicate component
            s = n[i];
            if x and s in ('','+','-') : s += '1';
            v[x] = float(s) if '.' in s or 'e' in s or 'n' in s else int(s);
            t = x;
          args = tuple(v);
        except :
          raise ValueError('invalid literal for quaternion()')
      elif iscomplex(args[0]) :
        args = (args[0].real,args[0].imag);
    if all(map(isreal,args)) :
      if len(args) == 2 :
        self.__v = (args[0],args[1],0,0);
      elif len(args) == 3 :
        self.__v = (0,args[0],args[1],args[2]);
      elif len(args) == 4 :
        self.__v = args;
      return self;
    raise TypeError('quaternion takes at most 4 reals or 1 complex');

  def __init__(self,*args) :
    """Do nothing--all the work has been done by __new__"""
    return;

  def __hash__(self) :
    """Return a hash for the quaternion; if convertible to complex, use that hash"""
    if not any(self.__v[2:]) :    # real or complex
      return hash(complex(*self.__v[0:2])) if self.__v[1] else hash(self.__v[0]);
    return hash(self.__v);

  def __bool__(self) :
    """Return True iff self != 0"""
    return any(self.__v);

  __nonzero__ = __bool__

  def __repr__(self) :
    """Return an evaluable string showing the quaternion"""
    return "quaternion('%r+%ri+%rj+%rk')"%self.__v;

  def __str__(self) :
    """Return a string showing the quaternion"""
    return '('+format(self.__v[0],'n')+format(self.__v[1],'+n')+'i'+\
        format(self.__v[2],'+n')+'j'+format(self.__v[3],'+n')+'k)';

  def __eq__(self,other) :
    """Return True iff self == other"""
    if isinstance(other,quaternion) :
      return self.__v == other.__v;
    elif isreal(other) :
      return self.__v[0] == other and \
          self.__v[1] == 0 and self.__v[2] == 0 and self.__v[3] == 0;
    elif isinstance(other,complex) :
      return self.__v[0] == other.real and self.__v[1] == other.imag and \
          self.__v[2] == 0 and self.__v[3] == 0;
    else :
      return False;

  def __ne__(self,other) :
    """Return True iff self != other"""
    return not self == other;

  def __lt__(self,other) :
    raise TypeError('no ordering relation is defined for quaternions');

  __le__ = __ge__ = __gt__ = __lt__;

  def __neg__(self) :
    """Return -self"""
    return quaternion(-self.__v[0],-self.__v[1],-self.__v[2],-self.__v[3]);

  def __invert__(self) :
    """Return conjugate of self"""
    return quaternion(self.__v[0],-self.__v[1],-self.__v[2],-self.__v[3]);

  conjugate = __invert__

  def __abs__(self) :
    """Return |self|"""
    return (self.__v[0]*self.__v[0]+self.__v[1]*self.__v[1]+
            self.__v[2]*self.__v[2]+self.__v[3]*self.__v[3])**.5;

  def versor(self) :
    """Return self/|self| or 1 if zero"""
    a = abs(self);
    return quaternion(*(x/a for x in self.__v) if a else (1,))

  def __add__(self,other) :
    """Return the sum self+other"""
    try :
      other = quaternion(other);
    except :
      return NotImplemented;
    return quaternion(*(a+b for a,b in zip(self.__v,other.__v)));

  __radd__ = __add__;

  __iadd__ = __add__;

  def __sub__(self,other) :
    """Return the difference self-other"""
    try :
      other = quaternion(other);
    except :
      return NotImplemented;
    return quaternion(*(a-b for a,b in zip(self.__v,other.__v)));

  __isub__ = __sub__;
 
  def __rsub__(self,other) :
    """Return the difference other-self"""
    try :
      other = quaternion(other);
    except :
      return NotImplemented;
    return quaternion(*(b-a for a,b in zip(self.__v,other.__v)));

  def __mul__(self,other) :
    """Return the product self*other"""
    try :
      other = quaternion(other);
    except :
      return NotImplemented;
    return quaternion(
      self.__v[0]*other.__v[0]
      -self.__v[1]*other.__v[1]-self.__v[2]*other.__v[2]-self.__v[3]*other.__v[3],
      self.__v[0]*other.__v[1]
      +self.__v[1]*other.__v[0]+self.__v[2]*other.__v[3]-self.__v[3]*other.__v[2],
      self.__v[0]*other.__v[2]
      +self.__v[2]*other.__v[0]+self.__v[3]*other.__v[1]-self.__v[1]*other.__v[3],
      self.__v[0]*other.__v[3]
      +self.__v[3]*other.__v[0]+self.__v[1]*other.__v[2]-self.__v[2]*other.__v[1]);

  __imul__ = __mul__;

  def __rmul__(self,other) :
    """Return the product other*self"""
    try :
      other = quaternion(other);
    except :
      return NotImplemented;
    return quaternion(
      other.__v[0]*self.__v[0]
      -other.__v[1]*self.__v[1]-other.__v[2]*self.__v[2]-other.__v[3]*self.__v[3],
      other.__v[0]*self.__v[1]
      +other.__v[1]*self.__v[0]+other.__v[2]*self.__v[3]-other.__v[3]*self.__v[2],
      other.__v[0]*self.__v[2]
      +other.__v[2]*self.__v[0]+other.__v[3]*self.__v[1]-other.__v[1]*self.__v[3],
      other.__v[0]*self.__v[3]
      +other.__v[3]*self.__v[0]+other.__v[1]*self.__v[2]-other.__v[2]*self.__v[1]);

  # danger: a*b**-1 != b**-1*a ?
  def __truediv__(self,other) :
    """Return the quotient self/other"""
    try :
      other = quaternion(other);
    except :
      return NotImplemented;
    return self*other.__pow__(-1);

  def __rtruediv__(self,other) :
    """Return the quotient other/self"""
    try :
      other = quaternion(other);
    except :
      return NotImplemented;
    return other*self.__pow__(-1);

  __itruediv__ = __truediv__

  __div__ = __truediv__
  __rdiv__ = __rtruediv__
  __idiv__ = __itruediv__

  def __pow__(self,other) :
    """Return self**other"""
    if not isinstance(other,NUMTYPE) :
      raise TypeError('exponent must be a number');
    r = other.real;
    if not any(self.__v) :      # special case zero
      if r > 0 : return self;
      else : raise ZeroDivisionError('0 cannot be raised to a nonpositive power');
    if r!=other or int(r)!=r :    # non integer power
      # a**x = exp(log(a)*x)
      return (self.log()*other).exp();
    r = int(r);    # integer power
    if not any(self.__v[1:]) :
      return quaternion(self.__v[0]**r);        #real
    if r < 0 :
      a = self.__v[0]*self.__v[0] + self.__v[1]*self.__v[1] + \
          self.__v[2]*self.__v[2] + self.__v[3]*self.__v[3];
      q = quaternion(self.__v[0]/a, -self.__v[1]/a, -self.__v[2]/a, -self.__v[3]/a);
      r = -r;
    else :
      q = self;
    result = quaternion(1,0,0,0);
    while r :
      if r&1 : result *= q;
      r >>= 1;        
      if not r : break;
      q *= q;
    return result;

  __ipow__ = __pow__

  def __rpow__(self,other) :
    """Return other**self"""
    if not isinstance(other,COMPLEXTYPE) :
      raise TypError('base must be a number');
    return quaternion(other).__pow__(self);

  # NOTE: might want to try to do a better pow computation by leaving
  # the divide to last and doing integer computations up to that point
  def exp(self) :
    """Return exp(self)"""
    ea = math.exp(self.__v[0]);
    av = math.sqrt(self.__v[1]*self.__v[1]+
                   self.__v[2]*self.__v[2]+
                   self.__v[3]*self.__v[3]);
    s = ea*math.sin(av)/av if av else 1;
    return quaternion(ea*math.cos(av),s*self.__v[1],s*self.__v[2],s*self.__v[3]);

  def log(self,base=math.e) :
    """Return the log of self to base base"""
    a = abs(self);
    av = math.sqrt(self.__v[1]*self.__v[1]+
                   self.__v[2]*self.__v[2]+
                   self.__v[3]*self.__v[3]);
    if not av and self.__v[0] < 0 :
      return quaternion(math.log(a,base),math.pi/math.log(base),0,0);
    ac = (math.acos(self.__v[0]/a)/av if av else 1./a)/math.log(base);
    return quaternion(math.log(a,base),ac*self.__v[1],ac*self.__v[2],ac*self.__v[3]);

  def __getattr__(self,name) :
    if name in ('sv','rv') :
      return self.__v;
    if name in ('s','r','real','scalar'):
      return self.__v[0];
    if name in ('v','vector') :
      return self.__v[1:];
    if name in ('i','imag') :
      return self.__v[1];
    if name == 'j' :
      return self.__v[2];
    if name == 'k' :
      return self.__v[3];
    raise AttributeError('quaternion object has no attribute '+name);

NUMTYPE = (int,long,float,complex,quaternion,) if VERSION2 else (int,float,complex,quaternion,);
