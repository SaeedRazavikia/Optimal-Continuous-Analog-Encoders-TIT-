#!/usr/bin/env python3
"""Certified synthesis for phi(s)=psi(s)=exp(s), pointwise peak P=1.

SciPy computes candidates. Fraction arithmetic independently verifies every
certificate; solver success and floating point eigenvalues are not certificates.
"""
from pathlib import Path
import json, math, argparse
from fractions import Fraction as F

ROOT=Path(__file__).resolve().parents[1]

def unpack(x):
    import numpy as np
    h,a,b,l1,l2,c,lam=x
    H=np.array([[h,l1,l2],[l1,a,c],[l2,c,b]])
    return H,H[1:,1:],lam

def pack(H,lam):
    import numpy as np
    return np.array([H[0,0],H[1,1],H[2,2],H[0,1],H[0,2],H[1,2],lam])

def solve_candidate(n=401):
    import numpy as np
    from scipy.optimize import minimize
    s=np.linspace(-1,1,n); Z=np.array([np.ones(n),s,np.exp(s)]).T
    ws=[np.array([-np.exp(-1),1.]),np.array([-np.exp(1),1.])]
    # Strictly feasible initial Gram.
    H0=np.diag([.02,.04,.04]); x0=pack(H0,.002)
    def con(x):
        H,G,lam=unpack(x)
        return np.r_[1-np.einsum('ni,ij,nj->n',Z,H,Z),np.linalg.eigvalsh(H),
          *[np.linalg.eigvalsh(G-lam*np.outer(w,w)) for w in ws],lam]
    res=minimize(lambda x:-x[-1],x0,jac=lambda x:np.array([0,0,0,0,0,0,-1.]),
      constraints={'type':'ineq','fun':con},method='SLSQP',
      options={'ftol':2e-13,'maxiter':1000,'disp':False})
    H,G,lam=unpack(res.x)
    q=np.einsum('ni,ij,nj->n',Z,H,Z)
    active=np.where(q>1-1e-7)[0]
    print('PRIMAL',res.success,res.message,'lambda',lam,'mincon',con(res.x).min())
    return res,s,Z,ws


def preliminary_dual(res,s,Z,ws):
    import numpy as np
    H,G,lam=unpack(res.x); m=res.multipliers; n=len(s)
    alpha=m[:n]
    mats=[]
    for j,w in enumerate(ws):
        vals,vecs=np.linalg.eigh(G-lam*np.outer(w,w))
        mats.append(sum(m[n+3+2*j+k]*np.outer(vecs[:,k],vecs[:,k]) for k in range(2)))
    D=np.einsum('n,ni,nj->ij',alpha,Z,Z)
    D[1:,1:]-=sum(mats)
    return alpha,mats

class Iv:
    """Closed rational interval, with exact endpoint arithmetic."""
    def __init__(self,lo,hi=None):
        self.lo=F(lo); self.hi=self.lo if hi is None else F(hi)
        assert self.lo<=self.hi
    def __add__(self,b):
        b=iv(b); return Iv(self.lo+b.lo,self.hi+b.hi)
    __radd__=__add__
    def __neg__(self): return Iv(-self.hi,-self.lo)
    def __sub__(self,b): return self+-iv(b)
    def __rsub__(self,b): return iv(b)+-self
    def __mul__(self,b):
        b=iv(b); terms=[self.lo*b.lo,self.lo*b.hi,self.hi*b.lo,self.hi*b.hi]
        return Iv(min(terms),max(terms))
    __rmul__=__mul__

def iv(x): return x if isinstance(x,Iv) else Iv(x)
def exp_iv(s):
    """Taylor degree 40; |remainder| <= e/41! < 3/41! for |s|<=1."""
    s=F(s); assert abs(s)<=1
    term=F(1); value=term
    for k in range(1,41):
        term*=s/k; value+=term
    rem=F(3,math.factorial(41))
    return Iv(value-rem,value+rem)

def eye(n): return [[F(i==j) for j in range(n)] for i in range(n)]
def zeros(n): return [[Iv(0) for j in range(n)] for i in range(n)]
def det(A):
    if len(A)==1: return iv(A[0][0])
    return sum(((-1)**j)*iv(A[0][j])*det([[row[k] for k in range(len(A)) if k!=j] for row in A[1:]]) for j in range(len(A)))
def pd_margins(A):
    assert len(A) in (2,3) and all(len(row)==len(A) for row in A), 'Expected square matrix of order 2 or 3'
    assert all(iv(A[i][j]).lo==iv(A[j][i]).lo and iv(A[i][j]).hi==iv(A[j][i]).hi for i in range(len(A)) for j in range(len(A))), 'Matrix is not symmetric'
    vals=[det([row[:k] for row in A[:k]]).lo for k in range(1,len(A)+1)]
    assert min(vals)>0, 'Positive definiteness not certified'
    return [float(x) for x in vals]
def rat(x,digits=12): return F(round(float(x)*10**digits),10**digits)
def ceil_rat(x,den=10**12): return F(-((-x.numerator*den)//x.denominator),den)
def rationalize(A,jitter=F(0)):
    return [[rat(x)+(jitter if i==j else 0) for j,x in enumerate(row)] for i,row in enumerate(A)]
def quadratic(z,H): return sum(iv(z[i])*H[i][j]*iv(z[j]) for i in range(len(z)) for j in range(len(z)))
def endpoint_ws(): return [[-exp_iv(-1),Iv(1)],[-exp_iv(1),Iv(1)]]
def z_iv(s): return [Iv(1),Iv(s),exp_iv(s)]
def score_margins(H,lam):
    return [pd_margins([[iv(H[i+1][j+1])-lam*w[i]*w[j] for j in range(2)] for i in range(2)]) for w in endpoint_ws()]
def encode_fracs(A): return [[str(x) for x in row] for row in A]
def decode_fracs(A): return [[F(x) for x in row] for row in A]

def certify_primal(H,lam,n):
    assert len(H)==3 and all(len(row)==3 for row in H), 'Expected 3x3 Gram matrix'
    assert lam>=0 and isinstance(n,int) and n>=2
    hm=pd_margins(H); gm=score_margins(H,lam)
    s=[F(-1)+F(2*k,n-1) for k in range(n)]
    peak=max(quadratic(z_iv(t),H).hi for t in s)
    grid_bound=ceil_rat(peak)
    # q''(s)=2 A+4 B exp(2s)+2 ell_2 exp(s)+2 C(s+2)exp(s).
    e=exp_iv(1).hi
    Mfrac=2*abs(H[1][1])+4*abs(H[2][2])*e*e+2*abs(H[0][2])*e+6*abs(H[1][2])*e
    M=ceil_rat(Mfrac,1)
    h=F(2,n-1); continuum_bound=grid_bound+M*h*h/8
    scale=1/continuum_bound
    lower=lam*scale
    return {'grid_points':n,'maximum_spacing':str(h),'grid_peak_upper':str(grid_bound),
        'second_derivative_bound':str(M),'continuum_peak_upper_before_scaling':str(continuum_bound),
        'scale':str(scale),'lower':str(lower),'lower_float':float(lower),
        'H_leading_minors_lower':hm,'score_leading_minors_lower':gm}

def dual_intervals(points,alphas,Bs):
    Q=zeros(3)
    for s,a in zip(points,alphas):
        z=z_iv(s)
        for i in range(3):
            for j in range(3): Q[i][j]+=a*z[i]*z[j]
    for B in Bs:
        for i in range(2):
            for j in range(2): Q[i+1][j+1]-=B[i][j]
    norm=sum(quadratic(w,B) for w,B in zip(endpoint_ws(),Bs))
    return Q,norm

def certify_dual(points,alphas,Bs):
    assert len(points)==len(alphas) and len(Bs)==2
    assert all(len(B)==2 and all(len(row)==2 for row in B) for B in Bs)
    assert all(a>=0 for a in alphas)
    bm=[pd_margins(B) for B in Bs]
    Q,norm=dual_intervals(points,alphas,Bs)
    qm=pd_margins(Q)
    assert norm.lo>=1, 'Dual score normalization is below one'
    upper=sum(alphas)
    return {'upper':str(upper),'upper_float':float(upper),
      'normalization_lower':float(norm.lo),'B_leading_minors_lower':bm,
      'Q_leading_minors_lower':qm}

def generate_certificate(nsolve=401,nverify=1001):
    import numpy as np
    res,s,Z,ws=solve_candidate(nsolve)
    Hf,Gf,lamf=unpack(res.x)
    H=rationalize(Hf,F(1,10**8)); lam=rat(lamf)-F(1,10**8)
    # Candidate primal repair is accepted only when exact interval tests pass.
    primal=certify_primal(H,lam,nverify)
    alpha0,B0=preliminary_dual(res,s,Z,ws)
    ii=np.where(alpha0>1e-10)[0]
    points=[F(-1)+F(2*int(i),nsolve-1) for i in ii]
    alphas=[rat(alpha0[i]) for i in ii]
    Bs=[rationalize(B,F(1,10**10)) for B in B0]
    # Normalize by a rational factor computed from an exact lower enclosure.
    _,norm=dual_intervals(points,alphas,Bs)
    scale=ceil_rat(1/norm.lo)+F(1,10**12)
    alphas=[a*scale for a in alphas]
    Bs=[[[v*scale for v in row] for row in B] for B in Bs]
    # Three anchor peak multipliers repair the dual residual. Their feature
    # vectors span R^3, so this succeeds for sufficiently large positive repair.
    repair=F(1,10**10)
    while True:
        pp=points+[F(-1),F(0),F(1)]; aa=alphas+[repair]*3
        try:
            dual=certify_dual(pp,aa,Bs); break
        except AssertionError:
            repair*=2
            if repair>F(1,100): raise RuntimeError('Dual repair too large')
    history=[certify_primal(H,lam,n) for n in [51,101,201,401,nverify]]
    lower=F(primal['lower']); upper=F(dual['upper'])
    cert={'problem':{'feature':'exp(s)','readout':'exp(m)','P':1,'K':'any integer >=4',
          'normalized_objective':'Lambda_sq/(K^2 P)'},
       'arithmetic':{'method':'exact rational interval arithmetic','exp_taylor_degree':40,
         'exp_remainder_bound':'3/41!','solver_role':'candidate generation only'},
       'candidate_solver':{'method':'SciPy SLSQP','grid_points':nsolve,'success':bool(res.success),
         'candidate_lambda':lamf,'message':res.message},
       'primal_witness':{'H':encode_fracs(H),'lambda':str(lam),'verification':primal},
       'dual_witness':{'points':[str(v) for v in pp],'weights':[str(v) for v in aa],
         'B_minus':encode_fracs(Bs[0]),'B_plus':encode_fracs(Bs[1]),
         'anchor_repair_each':str(repair),'verification':dual},
       'convergence_table':history,
       'certified_bounds':{'lower':str(lower),'upper':str(upper),'lower_float':float(lower),
         'upper_float':float(upper),'relative_gap_upper':float((upper-lower)/upper),
         'relative_gap_definition':'(upper-lower)/upper'}}
    return cert

def verify_certificate(cert):
    pw=cert['primal_witness']; dw=cert['dual_witness']
    p=certify_primal(decode_fracs(pw['H']),F(pw['lambda']),pw['verification']['grid_points'])
    d=certify_dual([F(s) for s in dw['points']],[F(a) for a in dw['weights']],
       [decode_fracs(dw['B_minus']),decode_fracs(dw['B_plus'])])
    assert p['lower']==cert['certified_bounds']['lower']
    assert d['upper']==cert['certified_bounds']['upper']
    assert F(p['lower'])<=F(d['upper'])
    return {'certificate_verified':True,**cert['certified_bounds']}

def figure(cert):
    import numpy as np
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    H=np.array([[float(F(v)) for v in row] for row in cert['primal_witness']['H']])
    scale=float(F(cert['primal_witness']['verification']['scale']))
    H*=scale; G=H[1:,1:]; ell=H[0,1:]; L=np.linalg.cholesky(G).T
    c=np.linalg.solve(L.T,ell)
    ss=np.linspace(-1,1,1001); E=c[:,None]+L@np.vstack([ss,np.exp(ss)])
    fig,ax=plt.subplots(1,2,figsize=(7.1,2.8))
    theta=np.linspace(0,2*np.pi,400)
    ax[0].plot(np.cos(theta),np.sin(theta),color='.7',linestyle='--',lw=.8,label='Peak boundary')
    ax[0].plot(*E,color='#15558f',lw=1.8,label='Certified encoder')
    ax[0].scatter(E[0,[0,-1]],E[1,[0,-1]],s=18,color='#15558f')
    ax[0].set(xlabel='Real component',ylabel='Imaginary component',aspect='equal')
    ax[0].legend(fontsize=7,loc='lower left')
    hist=cert['convergence_table']; upper=cert['certified_bounds']['upper_float']
    ns=[x['grid_points'] for x in hist]; gaps=[100*(upper-x['lower_float'])/upper for x in hist]
    ax[1].loglog(ns,gaps,'o-',color='#15558f',ms=4)
    ax[1].set(xlabel='Verification grid points',ylabel='Certified relative gap (%)')
    ax[1].grid(True,which='both',alpha=.25)
    fig.tight_layout()
    for ext in ['pdf','png']: fig.savefig(ROOT/'figures'/f'certified_synthesis.{ext}',dpi=200)
    plt.close(fig)
    return {'L':L.tolist(),'c':c.tolist(),
       'encoding':'E(s)=c+L (s, exp(s))^T; entries below are display approximations only',
       'normalized_score_lower':cert['certified_bounds']['lower_float']}

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--verify-only',action='store_true'); args=ap.parse_args()
    path=ROOT/'results'/'certified_synthesis.json'
    if args.verify_only:
        cert=json.loads(path.read_text()); print(json.dumps(verify_certificate(cert),indent=2)); return
    cert=generate_certificate()
    cert['reconstructed_encoder_display']=figure(cert)
    path.write_text(json.dumps(cert,indent=2)+'\n')
    print(json.dumps(verify_certificate(cert),indent=2))

if __name__=='__main__': main()
