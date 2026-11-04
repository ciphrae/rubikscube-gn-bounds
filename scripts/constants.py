"""Evaluate the two formulas proved in Lean. Nothing here is part of the proof."""
import math
Z=math.factorial(24)//24**6
def phase(r,c,s): return (r//s+1)*((2*s+4)*2**s+2*c)
def upperW(n,s): return 3*n+406+275*phase(n//2-1,n-n//2,s)
def best(n):
    L=n.bit_length()
    return min((upperW(n,s),s) for s in range(1,L+2))
def inner(n): return (n//2-1)*(n-n//2-1)
def lower(n):
    return (inner(n)*math.log2(Z)-6*math.log2(6))/math.log2(9*n+1)
if __name__=="__main__":
    print("log2 Z/4 =",math.log2(Z)/4," ln Z/4 =",math.log(Z)/4)
    print("%12s %14s %14s %8s %8s %5s"%("n","lower","upper","lo c","up c","s"))
    for n in [3,4,5,6,7,8,9,10,16,20,32,50,100,200,500,1000,10**4,10**5,10**6,10**9,10**12,2**40,2**64,2**100]:
        u,s=best(n); l=lower(n); x=math.log2(n)
        print("%12s %14.6g %14.6g %8.3f %8.1f %5d"%(n if n<10**13 else "2^%d"%round(x),max(l,0),u,max(l,0)*x/n**2,u*x/n**2,s))
    # L+1 version of the upper constant (what the simple proof uses)
    worst=0
    for n in range(3,4096):
        L=n.bit_length()-1; s=max(1,L//2)
        r=upperW(n,s)*(L+1)/n**2
        if r>worst: worst=r;wn=n
    print("worst upperW(n,max(1,L/2))*(L+1)/n^2 on [3,4096):",worst,"at",wn)
    for lo in (3,4,16,64,100,256,1000):
        print(lo, max(upperW(n,max(1,(n.bit_length()-1)//2))*(n.bit_length())/n**2 for n in range(lo,20000)))
