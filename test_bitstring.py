from __future__ import print_function
from __future__ import division

from conversions import xrange, bit_length

from random import Random, randrange, randint
from itertools import chain

from timeit import timeit, default_timer
from gc import collect

try:
  from timer import process_time
except Exception :
  process_time = default_timer;

from bitstring import bitstrings, _CB, bitstring

from ffield import ffield
from poly import polynomial as poly

GF2 = ffield(2);

def bitstring2poly(b) :
  """Return GF(2) polynomial representing bitstring, p[i] = b[i]"""
  return poly(*b[::-1]).mapcoeffs(GF2);

b2p = bitstring2poly;

def poly2bitstring(p,n=None) :
  """Return |n|-bit bitstring representing GF(2) polynomial, b[i] becomes p[i],
  if n is 0, len(b) = max(0,p.degree+1), if n is negative, b[i+n] becomes p[i]"""
  return bitstring(p.mapcoeffs(int)(2),-(n or max(0,p.degree+1)));

p2b = poly2bitstring;

def polyconv(a,b,n=0) :
  """Return a*b%(x^n-1), with n = max(n,1+a.degree,1+b.degree) """
  n = max(n,1+a.degree,1+b.degree);
  return a*b%(poly(1,*(0 for _ in range(n-1)),-1).mapcoeffs(GF2));

pc = polyconv;

bm = lambda a,b: p2b(pc(b2p(a),b2p(b),len(a)),len(a));

def b3x(b) :
  """transform string-based bitstring for sha3 input/output"""
  l = b._l;
  for i in xrange(0,l+7,8) :
    b[i:i+8] = b[i+7:i-1 if i else None:-1];
  return b;

def ceq(c,*v) :
  try :
    if not eval(c,locals()) :
      print(c,v);
  except Exception :
    print(c,v);
    raise;

maxbits = 1024;    # maximum number of bits in random arguments

def test1(bs) :
  """test single bitstring type"""
  l = randint(0,maxbits);    # size of bitstring
  m = (1<<l)-1;    # bitstring mask
  x = randrange(1<<l);
  b = bs(x,l);
  ceq('v[0]==+v[0]',b);
  ceq('0-v[0]==-v[0]',b);
  ceq('v[0]^-1==~v[0]',b);
  ceq('len(v[0])==v[1]',b,l);
  ceq('int(v[0])==v[1]',b,x);
  ceq('v[0].concat(0,1)[:-2]==v[0]',b);
  ceq('int(v[0].concat(0,1)[-2:])==1',b);
  ceq('v[0].concat(v[0])==v[0]*2',b);
  ceq('v[0]*-1==v[0][::-1]',b);
  ceq('v[0]*0==type(v[0])()',b);
  ceq('len(v[0]*3)==len(v[0]*-3)==len(v[0])*3',b);
  i = randint(1,64);
  ceq('len(v[0].split(v[1]))==(v[2]+v[1]-1)//v[1]',b,i,l);
  ceq('len(v[0].split(-v[1]))==(v[2]+v[1]-1)//v[1]',b,i,l);
  if l :
    ceq('all(len(x)==v[1] for x in v[0].split(v[1])[:-1])',b,i);
    ceq('all(len(x)==v[1] for x in v[0].split(-v[1])[1:])',b,i);
    ceq('v[0]==type(v[0]).iconcat(*v[0].split(v[1]))',b,i);
    ceq('v[0]==type(v[0]).iconcat(*v[0].split(-v[1]))',b,i);
    i = randint(0,l);
    ceq('v[0]==v[0][:v[1]].concat(v[0][v[1]:])',b,i);
    ceq('v[0]==v[0][v[1]:].tacnoc(v[0][:v[1]])',b,i);
    ceq('v[0]<<v[1]==v[0][v[1]:].concat(v[0][:v[1]])',b,i);
    ceq('v[0]<<v[1]==v[0]>>(len(v[0])-v[1])',b,i);
    ceq('v[0].trunc(v[1])==v[0][:v[1]]',b,i);
    ceq('v[0]<<v[1]==v[0][v[1]:].concat(v[0].trunc(v[1]))',b,i);
    ceq('v[0]==v[0].trunc(len(v[0])+v[1]).trunc(len(v[0]))',b,i);
    ceq('v[0][:].itrunc(v[1])==v[0].trunc(v[1])',b,i);
    ceq('v[0][:].itrunc(-v[1])==v[0].trunc(-v[1])',b,i);
    ceq('v[0][:].itrunc(v[1])==v[0].trunc(v[1])',b,i+l);
    ceq('v[0][:].itrunc(-v[1])==v[0].trunc(-v[1])',b,i+l);
    if i :
      ceq('v[0].trunc(-v[1])==v[0][-v[1]:]',b,i);
    j = randint(0,l);
    if i > j : i,j=j,i;
    c = bs(b);    # copy of b
    c[i:j] = ~b[i:j];    # usually munge c
    if i < j :
      ceq('v[0]!=v[1]',b,c);
    c[i:j] = b[i:j];    # should restore c
    ceq('v[0]==v[1]',b,c);
    ceq('int(v[0][v[1]:v[2]])==(int(v[0])>>(len(v[0])-v[2]))&((1<<(v[2]-v[1]))-1)',b,i,j);
    ceq('v[0]==v[0][:v[1]].concat(v[0][v[1]:v[2]],v[0][v[2]:])',b,i,j);
  # test operations:
  y = randrange(1<<l);
  c = bs(y,l);
  ceq('int(v[0]^v[1])==v[2]',b,c,x^y);
  ceq('int(v[0]|v[1])==v[2]',b,c,x|y);
  ceq('int(v[0]&v[1])==v[2]',b,c,x&y);
  ceq('int(v[0]+v[1])==v[2]',b,c,(x+y)&m);
  ceq('int(v[0]-v[1])==v[2]',b,c,(x-y)&m);
  ceq('v[0]*v[1]==v[2]',b,c,bm(b,c));

def test2(b1,b2) :
  """test pairs of bitstring types"""
  l = randint(0,maxbits);   # size of bitstring
  x = randrange(1<<l);
  b = b1(x,l);
  c = b2(x,l);
  ceq('v[0]==v[1]',b,c);
  ceq('v[0]<=v[1]',b,c);
  ceq('not v[0]<v[1]',b,c);
  ceq('v[0]<=v[1].concat(0)',b,c);
  ceq('v[0]<v[1].concat(0)',b,c);
  ceq('not v[0].concat(0)<=v[1]',b,c);
  ceq('v[0]>=v[1]',b,c);
  ceq('not v[0]>v[1]',b,c);
  ceq('not v[0]>=v[1].concat(0)',b,c);
  ceq('v[0].concat(0)>v[1]',b,c);
  ceq('v[0].concat(0)>=v[1]',b,c);
  if l :
    ceq('not v[0]^1<v[1]',b,c);
    ceq('not v[0]^1<=v[1]',b,c);
    ceq('not v[0]^1>v[1]',b,c);
    ceq('not v[0]^1>=v[1]',b,c);
  ceq('int(v[0]^v[1])==0',b,c);
  ceq('int(v[0]-v[1])==0',b,c);
  ceq('int(v[0]+-v[1])==0',b,c);
  ceq('v[0]|v[1] == v[0]',b,c);
  ceq('v[0]&v[1] == v[0]',b,c);
  ceq('int(v[0]&~v[1]) == 0',b,c);
  ceq('int(~(v[0]|~v[1])) == 0',b,c);
  ceq('int(v[0].concat(v[1]))==int(v[0])*((1<<len(v[0]))+1)',b,c);


R=Random();
R.seed(0);

# what should we time?
# (0) getitem, setitem: single bit, consecutive bits, random bits
# (1) each of the ops (& | ^ + -)
# (2) rotations of various amounts (<< >>)
# (2) conversion between bitstring types
# (3) concatenation
# (4) truncation
# (5) scalar multiplication (*)
# (6) b3x

def timetest1(B) :
  timing('create',B,B,'x,y=3**646,1024','bb(x,y)');
  timing('int',B,B,'b=bb(3**646,1024)','int(b)');
  timing('*-1',B,B,'b=bb(3**646,1024)','b*-1');
  timing('getone',B,B,'b=bb(3**646,1024)','b[0]');
  timing('getall',B,B,'b=bb(3**646,1024)','b[:]');
  timing('getmid',B,B,'b=bb(3**646,1024)','b[256:768]');
  timing('getalt',B,B,'b=bb(3**646,1024)','b[::2]');
  timing('*2',B,B,'b=bb(3**646,1024)','b*2');
  timing('b3x',B,B,'b=bb(3**646,1024)','b3x(b)');
  timing('shift1',B,B,'b=bb(3**646,1024)','b<<=1');
  timing('shifth',B,B,'b=bb(3**646,1024)','b<<=512');
  timing('trunch',B,B,'b=bb(3**646,1024)','b.trunc(511)');
  timing('trunc-h',B,B,'b=bb(3**646,1024)','b.trunc(-511)');
  timing('itrunc',B,B,'b=bb(3**646,1024)','b.itrunc(511)');
  timing('itrunc-',B,B,'b=bb(3**646,1024)','b.itrunc(-511)');  


def timetest2(B,C) :
  timing('convert',B,C,'b=bb(3**646,1024)','bc(b)');
  timing('concat',B,C,'b=bb(3**646,1024);c=bc(5**441,1024)','b.concat(c)');
  timing('xor',B,C,'b=bb(3**646,1024);c=bc(5**441,1024)','b^c');
  timing('and',B,C,'b=bb(3**646,1024);c=bc(5**441,1024)','b&c');
  timing('or',B,C,'b=bb(3**646,1024);c=bc(5**441,1024)','b|c');
  timing('add',B,C,'b=bb(3**646,1024);c=bc(5**441,1024)','b+c');
  timing('sub',B,C,'b=bb(3**646,1024);c=bc(5**441,1024)','b-c');
  timing('mul',B,C,'b=bb(3**646,1024);c=bc(5**441,1024)','b*c');
  timing('iconcat',B,C,'b=bb(3**646,1024);c=bc(5**441,1024)','b.iconcat(c)');
  timing('ixor',B,C,'b=bb(3**646,1024);c=bc(5**441,1024)','b^=c');
  timing('iand',B,C,'b=bb(3**646,1024);c=bc(5**441,1024)','b&=c');
  timing('ior',B,C,'b=bb(3**646,1024);c=bc(5**441,1024)','b|=c');
  timing('iadd',B,C,'b=bb(3**646,1024);c=bc(5**441,1024)','b+=c');
  timing('isub',B,C,'b=bb(3**646,1024);c=bc(5**441,1024)','b-=c');
  timing('imul',B,C,'b=bb(3**646,1024);c=bc(5**441,1024)','b*=c');
  timing('split',B,C,'b=bb(7**365,1025)','b.split(bc._B)');
  timing('split-',B,C,'b=bb(7**365,1025)','b.split(-bc._B)');
  
def timing(name,B,C,setup,stmt,repeat=1000) :
  """Print time taken by stmt"""
  collect();
  t = timeit(
    stmt=stmt,
    setup='from test_bitstring import bitstrings,inf,b3x\nbb=bitstrings(%s)\nbc=bitstrings(%s)\n%s'%(B,C,setup),
    timer=process_time,number=repeat);
  print('%s\t%.3f ms'%(name,t/repeat*1000));

inf = float('inf');
bss = (1,8,30,31,32,64,inf);

if __name__=='__main__' :

  def usage() :
    print("""
Usage: python test_bitstring.py [options]
   Options:  -h        print this message
             -o        omit operation testing
             -t n      0->no timing, 1->only single B timing, 2->all timing [default]
             -m b      max number of bits in random op test args [default: %d]
             -c s      threshold chunk size in bits [default: %d]
"""%(maxbits,_CB));

  import sys,getopt
  opts,args = getopt.gnu_getopt(sys.argv[1:],"hot:m:c:");
  optdict = {};
  for pair in opts : optdict[pair[0][1:]]=pair[1];
  if 'h' in optdict :
    usage();
    if len(optdict) < 2 : sys.exit();
  maxbits = int(optdict.get('m',maxbits));
  if not 'o' in optdict :
    for B in bss :
      print(' %s'%(B));
      for _ in xrange(256) :
        test1(bitstrings(B));
        for C in bss :
          test2(bitstrings(B),bitstrings(C))
  _CB = int(optdict.get('c',_CB));
  t = int(optdict.get('t',2));
  if t :
    for B in bss :
      print(' %s'%(B));
      timetest1(B);
      if t < 2 :
        timetest2(B,B);
      else :
        for C in bss :
          print('  %s'%(C));
          timetest2(B,C);
