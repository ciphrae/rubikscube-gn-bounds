"""Compare the proved closed forms with the exact proved formulas, per n^2/log2 n."""
import math,sys
sys.path.insert(0,'scripts')
from constants import upperW,inner,Z
def best(n):
    L=n.bit_length()
    return min(upperW(n,s) for s in range(1,L+2))
print("%6s | %8s %8s | %8s %8s %8s | %6s"%("log2 n","lo exact","lo form","up exact","up form","c=1.914","c need"))
LZ=math.log2(Z)
for x in (16,20,24,32,40,64,100,200,500,1000,4000):
    n=2**x
    # scaled by n^2 in exact integer arithmetic
    lo_e=inner(n)*LZ/n**2/math.log2(9*n+1)*x if False else None
    i=(inner(n)<<40)//n**2/2**40
    lo_exact=(i*LZ)/(x+math.log2(9))*x
    lo_form=12.88*x/(x+3.18)
    u=best(n); up_exact=(u<<40)//n**2/2**40*x
    D=x-2*math.log2(x)
    up_form=137.5*x/(D-4); up_sharp=137.5*x/(D-1.914)
    print("%6d | %8.3f %8.3f | %8.2f %8.2f %8.2f | %6.3f"%(x,lo_exact,lo_form,up_exact,up_form,up_sharp,D-137.5*x/up_exact))
