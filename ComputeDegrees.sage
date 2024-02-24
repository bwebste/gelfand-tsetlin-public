import itertools

def ComputeDegree(sigma):
    deg=0
    length =0
    for i in range(len(sigma)):
        pi =sigma[i]
        for j in range (1,i+2):
            for q in range (j+1,i+2):
                if pi(q) < pi(j): 
                    deg+=-2
                    length+=1
        if i<len(sigma)-1:
            pj =sigma[i+1]
            for j in range (1,i+2):
                for k in range(1,j+1):
                    if pj(k) > pi(j): deg+=1
                for k in range(j+1,i+3):
                    if pj(k) < pi(j)+1: deg+=1
        if i==len(sigma)-1:
            for j in range (1,i+2):
                deg=deg+abs(pi(j)-j)
    return (deg,length)

def DegreePairs(sigma):
    pairs = []
    for i in range(len(sigma)):
        pi =sigma[i]
        if i<len(sigma)-1: pj =sigma[i+1]
        if i>0: pm =sigma[i-1]
        for j in range (1,i+2):
            for q in range (j+1,i+2):
                #print(i+1,j,q);
                if pi(q) < pi(j): 
                    #print(j,q)
                    deg=-2
                    for h in range(j+1,q):
                        if pi(h) < pi(j) and pi(h) > pi(q): deg+=-4
                    if i>0: 
                        for h in range(j,q):
                            if pm(h) < pi(j) and pm(h) > pi(q)-1: deg+=2
                        #print(sigma,j,h,q,deg)
                    if i<len(sigma)-1:
                        for h in range(j+1,q+1):
                            if pj(h) < pi(j)+1 and pj(h) > pi(q): deg+=2
                        #print(sigma,j,h,q,deg)
                    if i==len(sigma)-1:
                        for h in range(j+1,q+1):
                            if h < pi(j)+1 and h > pi(q): deg+=2
                        #print(sigma,j,h,q,deg)
                    if deg >=0: pairs.append((i+1,j,q,deg))
    return pairs

def AllPermutations(n):
    return itertools.product(*[list(Permutations(i)) for i in range(1,n+1)])

def TestAllPermutations(n,verbose):
    degrees=[]
    for sigma in AllPermutations(n-1):
        deg=ComputeDegree(sigma)[0]
        length=ComputeDegree(sigma)[1]
        if deg < 0: print("Whoa, that's a negative degree at ",sigma)
        if deg > len(degrees)-1: degrees.extend([0]*(deg-len(degrees)+1))
        #print(sigma,ComputeDegree(sigma))
        degrees[deg]=degrees[deg]+1
        if verbose==True: print (sigma,deg,degrees)
    return degrees
        
