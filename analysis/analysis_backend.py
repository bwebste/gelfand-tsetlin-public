########################################################################
# for turning strings into polynomials
from sympy.parsing.sympy_parser import parse_expr

# for treating q as a symbolic variable in polynomials
from sympy import symbols
q=symbols("q")

# for getting integer adding list elements together 
from functools import reduce

# turn this on if you want more feedback, it's a lot (you've been warned)
verbose = False 
########################################################################

# function to turn an MVP in rawData into [ [p_1(q),e_1], [p_2(q),e_2],...] format
def reformatMVP(mvp):

	# split mvp term-by-term by using "]" as separator
	# NOTE: this gives one extra entry in list and removes "]" entirely
	# we remove redundant last entry and put back in the "]"

	mvp = mvp.split("]")
	if verbose: print("after ] split: ",mvp,"\n")
	mvp.pop(len(mvp)-1)
	if verbose: print("after pop len -1: ",mvp,"\n")
	mvp = list(map(lambda x: x + "]",mvp))
	if verbose: print("after giving back ] ", mvp,"\n")
	
	# split each entry into p_i(q) and e_i
	# remove redundant first entry
	# put back in "[" 
	mvp = list(map(lambda x: x.split("["),mvp))
	if verbose: print("after splitting at [ ", mvp,"\n")
	#mvp.pop(0)
	#print("after pop (0) ", mvp,"\n")
	mvp = list(map(lambda x: [x[0], "[" + x[1]] ,mvp))
	if verbose: print("after giving back [ ", mvp,"\n")
	
	# each p_i starts redundant "+" char, we remove this
	mvp = list(map(lambda x: [x[0][1::],x[1]] if x[0] == '+' else x,mvp))
	
	if verbose: print("after trimming + ", mvp,"\n")

	# if i-th Laurent polynomial equaled 1 then p_i(q) = "" at the moment
	# we need to manually set p_i(q) = 1
	mvp = list(map(lambda x: ["1",x[1]] if x[0] == ''  else x, mvp))
	if verbose: print("after setting trivial p_i to 1 + ", mvp,"\n")

	# reformat p_i so that q^n -> q**n (python only knows second one)
	mvp = list(map(lambda x: [x[0].replace("^","**"),x[1]],mvp))
	if verbose: print("after changing ^ to ** ", mvp,"\n")
	
	# p_i is a string, make it a sympy polynomial
	mvp = list(map(lambda x: [parse_expr(x[0]),x[1]],mvp))
	if verbose: print("after converting to sympy ", mvp,"\n")

	# remove "[" and "|" and "]" character in the e_i
	mvp = list(map(lambda x: [x[0],x[1].replace("|","").replace("[","").replace("]","")],mvp))

	return mvp

# compute dimension of simple by evaluating Laurent polynomials at q=1
def getDimension(simple):
	# record only polynomials, the idempotents are irrelevant now
	polys = list(map(lambda x : x[0], simple))

	# evaluate each polynomial at q=1
	evaluated_at_1 = list(map(lambda x: x.subs(q,1),polys))

	# add polynomials
	return int(reduce(lambda x,y : x+y, evaluated_at_1))

# check for an idempotent that has "22" subword and "33" subword but not "333" subword, and its Laurent polynomial is not q**2 + 2 q**-2
def hasNilHeckeAndCoolLaurent(mvp):
	hasNilHecke = False
	for term in mvp:
		if "22" in term[1] and "33" in term[1] and "333" not in term[1]:
			if term[0] != q**2 + 2 + q**-2:
				hasNilHecke = True
	return hasNilHecke

# same as pervious but verbose
def showNilHeckeAndCoolLaurent(mvp):
	hasNilHecke = False
	print("Checking : \n",mvp,"\n")
	for term in mvp:
		if "22" in term[1] and "33" in term[1] and "333" not in term[1]:
			if term[0] != q**2 + 2 + q**-2:
				hasNilHecke = True
				print("The idempotent ", term[1], " is a candidate.")
				print("   successful candidate because ", term[0], " is not q**2 + 2 + q**-2.")
	print("\n\n\n")
	return hasNilHecke

import re

def GKdimension(mvp):
    GK = 0
    for term in mvp:
        x=re.sub("4.*4","",term[1])
        if len(x) > GK:
            GK = len(x)
    return GK
def arePermutation(str1, str2): 
      
    # Get lenghts of both strings 
    n1 = len(str1) 
    n2 = len(str2) 
  
    # If length of both strings is not same, 
    # then they cannot be Permutation 
    if (n1 != n2): 
        return False
  
    # Sort both strings 
    a = sorted(str1) 
    str1 = " ".join(a) 
    b = sorted(str2) 
    str2 = " ".join(b) 
  
    # Compare sorted strings 
    for i in range(0, n1, 1): 
        if (str1[i] != str2[i]): 
            return False
  
    return True

def infdim(mvp):
    for term in mvp:
        seq = term[1]
        for i in range(len(seq)):
            if seq[i]=='4':
                break
            if sorted(seq[:i])==sorted(seq[-i:]):
                return True
    return False

def mult(seq,mvp):
    for term in mvp:
        if term[1]==seq:
            m= term[0].subs(q,1)
            return m
    return 0

def NonzeroMults(seq, simples):
    mults=[]
    for mvp in simples:
        k=mult(seq,mvp)
        if not k==0:
            mults.append(k)
    return sorted(mults)

def AllMults(simples):
    allmults=[]
    k=0
    for mvp in simples:
        print(k)
        k=k+1
        for w in mvp:
            seq=w[1]
            m=NonzeroMults(seq,simples)
            new=True
            for option in allmults:
                if m==option[0]:
                    new=False
            if new:
                allmults.append([m,seq])
    return allmults

