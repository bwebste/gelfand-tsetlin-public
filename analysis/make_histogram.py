from analysis import *
import matplotlib.pyplot as plt


dims = list(map(lambda x: getDimension(x),simples))

plt.hist(dims,40)
plt.title("Dimension of simples")
plt.xlabel("Dimension")
plt.ylabel("Number of irreps")
plt.savefig("dimension_hist.png")
plt.clf()

def small_dimension(dim):
	return dim < 100

smalldims = list(filter(small_dimension,dims))
plt.hist(smalldims,15)
plt.title("Dimension of small simples")
plt.xlabel("Dimension")
plt.ylabel("Number of irreps")
plt.savefig("small_dimension_hist.png")
plt.clf()

GKs = list(map(lambda x:  GKdimension(x),simples))
idGKs= list(map(lambda x:  GKdimension(x),idsimples))
fdGKs = list(map(lambda x:  GKdimension(x),fdsimples))
plt.hist([fdGKs,idGKs],bins=[0,1,2,3,4,5,6,7],align='left',stacked=True)
plt.title("Gelfand-Kirillov dimensions")
plt.xlabel("GK dimension")
plt.ylabel("Number of irreps")
plt.savefig("GK_dimension_hist.png")
plt.clf()

