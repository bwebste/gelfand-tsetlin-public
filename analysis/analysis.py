#######################################################################
# Tools to load irreducible characters from GAP and check for patterns


# load backend for this library 
from analysis_backend import *

########################################################################

# name of input file to be analyzed
inputFile= "gl4_results_readable.txt" 

# load inputFile 
rawData = open(inputFile,"r").read()

# remove linebreaks and spaces from list of MVPs
rawData = rawData.replace(" ","")
rawData = rawData.replace("\n","")

# trim first char = "[" and last char = "]" (they are not needed)
rawData= rawData[1:-1]

# turn string of MVPs into list of MVPs by splitting at comma
rawData = rawData.split(",")

# convert each MVP m = p_1(q) [e_1] + p_2(q)[e_2] + ...  -> [ [p_1(q),e_1], [p_2(q),e_2],...]  
# p_i(q)		:		Laurent polynomial from i-th term in MVP 
# e_i				:		good word [.|...|.] corresponding to i-th term in MVP	
simples = list(map(lambda x: reformatMVP(x),rawData))

# subset of the simples with at least one idempotent satisfying 
# (a) has a 22 and 33 but not 333 
# (b) it's Laurent polynomial is not q**2 + 2 + q**-2
#interestingSimples = list(filter(hasNilHeckeAndCoolLaurent,simples))

idsimples = list(filter(infdim,simples))
fdsimples = list(filter(lambda x: not infdim(x),simples))
isinfdim = list(map(lambda x: infdim(x),simples))

idGKdims = list(map(lambda x: GKdimension(x),idsimples))
fdGKdims = list(map(lambda x: GKdimension(x),fdsimples))
GKdims = list(map(lambda x: GKdimension(x),simples))

############Notes
#simples 7 and 97 are good for testing

def idprint(i):
    mind=isinfdim[30*i:30*(i+1)]
    return mind
#psble= AllMults(simples)

for i in range(240,259):
    print(i,simples[i][0][1])


for i in range(29,259,30):
    print(i,simples[i][0][1])
