#!/usr/bin/env python3
"""Exact rational checks for the algebraic certificates in Appendix A.

Run with Python 3 and SymPy. All proof checks use rational arithmetic;
no floating-point samples are used to establish polynomial positivity.
The full coefficient lists and a concise report are written beside this file.
"""
from pathlib import Path
import csv
import json
import sympy as sp

OUT = Path(__file__).resolve().parent
Q = sp.Rational
c,h,n,k,v,r = sp.symbols('c h n k v r')
report = {}

def check_zero(name, expr):
    reduced = sp.cancel(expr)
    assert reduced == 0, (name, reduced)
    report[name] = True

G = (1+(1-h)*(2*c-1)/2
     +(1-h)*(1-2*h)*(3*c**2-3*c+1)/6
     +(1-h)*(1-2*h)*(1-3*h)*(4*c**3-6*c**2+4*c-1)/24)
A4 = Q(37,64)*c+Q(7,32)*(1-h)*c**2+Q(1,24)*(1-h)*(1-2*h)*c**3
T4 = c**4*sp.prod(1-j*h for j in range(1,5))/(24*(1-c/5))
F4 = Q(81,256)-A4-T4/4
y=Q(1,2)-c
R0=1+13*y+y**2*(1732-728*y-552*y**2)
R1=48+y*(114+1636*y+1128*y**2+2000*y**3)
R2=-240+c*(1008-1632*c+c**2*(1248-2392*c))
check_zero('fourth_node_identity', F4+(4-h)/(5*(1-h))*(G-1)
           -(1-4*h)/(3840*(5-c))*(R0+h*R1+h**2*R2+1200*c**4*h**3))

q2=2*c
q3=Q(15,8)*c+Q(9,16)*(1-h)*c**2
q4=Q(148,81)*c+Q(56,81)*(1-h)*c**2+Q(32,243)*(1-h)*(1-2*h)*c**3
check_zero('node_difference_3_2', q3-q2-c*(9*(1-h)*c-2)/16)
check_zero('node_difference_4_3', q4-q3-c*(501*(1-h)*c+512*(1-h)*(1-2*h)*c**2-186)/3888)

a=k/(k+c)
delta=c/(k+c)
tau=3/(6*n+4)
An=1+tau+tau**2/2+tau**3/6
B=1+(k-1)*delta/n+(k-1)*(k-2)*delta**2/(2*n**2)
C=1+(Q(1,2)-c)/k+1/(12*k**2)
def zhat(t,u):
    return u*(19*t+4*u)/(20*t*(t-u))
def phi(nn,kk,cc):
    return (An*B*C-1-zhat(n+1,a)).subs({n:nn,k:kk,c:cc}, simultaneous=True)

boundary=sp.diff(B*C,c).subs(n,k-2)*2*k*(k-2)*(k+c)**3
boundary_claim=((3-6*c)*k**3+(-Q(5,6)+14*c-15*c**2)*k**2
                +(-Q(1,6)-Q(5,3)*c+21*c**2-5*c**3)*k+c*(7*c**2-Q(1,3)))
check_zero('derivative_boundary_identity', boundary-boundary_claim)

# Nonnegative coefficients of the two positive c-polynomials can be checked
# on c in [11/24,1/2] after affine rescaling, or by elementary bounds in text.
t,u=sp.symbols('t u')
Gn=t-2*u+(t-u)*zhat(t,u)-19*u/(20*zhat(t,u))
check_zero('target_substitution_identity', Gn-3*u/20-u*(t-4*u)*(t-u)/(5*t*(19*t+4*u)))

d=6*n+4
K=24*k+11
U=(n+1)*K-24*k
P=sp.cancel(Q(5,124416)*d**3*k**2*n**3*K**2*(n+1)*U*(phi(n,k,Q(11,24))-1/(500*n**3)))
assert sp.denom(P)==1, 'P is not a polynomial'
Pshift=sp.Poly(sp.expand(P.subs({n:5+v,k:7+v+r}, simultaneous=True)),r,v,domain=sp.QQ)
assert all(cc>0 for cc in Pshift.coeffs()), 'A P coefficient is not positive'
summary=[]
coefficients=[]
for j in range(6):
    pj=sp.Poly(Pshift.as_expr().coeff(r,j),v,domain=sp.QQ)
    cs=list(reversed(pj.all_coeffs()))
    assert all(cc>0 for cc in cs), (j,cs)
    summary.append({'j':j,'degree':pj.degree(),'minimum_coefficient':str(min(cs))})
    for i,cc in enumerate(cs):
        coefficients.append((j,i,str(cc)))
assert [row['degree'] for row in summary] == [12,11,10,9,8,7]
assert [row['minimum_coefficient'] for row in summary] == ['6','25','40','30','10','1']
report['P_coefficients']=summary
with (OUT/'P_coefficients.csv').open('w',newline='') as f:
    writer=csv.writer(f); writer.writerow(['power_of_r','power_of_v','coefficient']);writer.writerows(coefficients)

K4=(3*k+1)*(8*k+1)
U4=5*K4-24*k**2
cdag=Q(11,24)+1/(24*k)
P4=sp.cancel(Q(5488000,56441883)*k**2*K4**2*U4*(phi(4,k,cdag)-Q(1,4000)))
assert sp.denom(P4)==1, 'P4 is not a polynomial'
P4shift=sp.Poly(P4.subs(k,6+r),r,domain=sp.QQ)
p4cs=list(reversed(P4shift.all_coeffs()))
assert all(cc>0 for cc in p4cs), p4cs
assert P4shift.degree() == 8 and min(p4cs) == 1
report['P4_coefficients']={'degree':P4shift.degree(),'minimum_coefficient':str(min(p4cs)),
                           'coefficients_in_ascending_order':[str(cc) for cc in p4cs]}
with (OUT/'P4_coefficients.csv').open('w',newline='') as f:
    writer=csv.writer(f);writer.writerow(['power_of_r','coefficient']);writer.writerows(enumerate(map(str,p4cs)))

report['all_exact_checks_passed']=True
(OUT/'verification_results.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
