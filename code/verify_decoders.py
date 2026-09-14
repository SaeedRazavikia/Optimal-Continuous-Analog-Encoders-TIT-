"""Fresh numerical verification of rebuilt projection-decoder implementations."""
from pathlib import Path
import json,platform,hashlib
from datetime import datetime,timezone
import numpy as np
import scipy
from scipy.optimize import minimize
from decoders import *
root=Path(__file__).resolve().parents[1]
rng=np.random.default_rng(20260913); checks=[]; samples=[]
def check(name,value,tol):
 checks.append(dict(name=name,residual=float(value),tolerance=tol,passed=bool(np.isfinite(value) and value<=tol)))
for target,p,M in [('variance',2,2),('quartic_jensen',4,4),('mq',2,1)]:
 a,b,c0=quartic(4)[1:] if p==4 else quadratic(M)
 lam=1/(M*M/a**2+1/b**2)
 for K in (4,7,19):
  X=rng.uniform(-1,1,(64,K));X[:3]=np.array([-1,0,1])[:,None]
  m=X.mean(1);t=(X**p).mean(1); f=m*t if target=='mq' else t-m**p
  for P in (.04,1,9):
   c=np.sqrt(P)*np.array([0,c0]);B=np.sqrt(P)*np.diag([a,b]);r=encode(X,c,B,p).sum(1)
   fun=(lambda y:decode_mq(y,K,P,a,b)) if target=='mq' else (lambda y:decode_gap(y,c,B,K,lambda m:m**p))
   L=1/(K*np.sqrt(P*lam)); angle=np.arange(64)*np.pi*(3-np.sqrt(5));radius=np.geomspace(1e-6,1e3,64)*K*np.sqrt(P)
   n=radius[:,None]*np.column_stack((np.cos(angle),np.sin(angle)))
   err=np.abs(fun(r+n)-f); bound=L*radius
   check(f'{target} exact K{K} P{P}',np.max(np.abs(fun(r)-f)),3e-14)
   check(f'{target} uniform bound K{K} P{P}',max(0,np.max(err-bound)),5e-12)
   if target!='mq': check(f'{target} constant K{K} P{P}',abs(constant(B,K,(-p,p))-L),1e-13)
   for i in range(64):samples.append(dict(target=target,K=K,P=P,error=float(err[i]),bound=float(bound[i])))
B=np.array([[.6,.17],[-.13,.45]]);c=np.array([.1,-.2]);K=7; row=np.linalg.inv(B)[0]
errors=[]
for i in range(24):
 y=rng.normal(size=2)*20
 coordinates=strip_coordinates(y,c,B,K);expected=K*c+K*B@coordinates
 cons=[{'type':'ineq','fun':lambda x:K-row@(x-K*c),'jac':lambda x:-row},
       {'type':'ineq','fun':lambda x:K+row@(x-K*c),'jac':lambda x:row}]
 res=minimize(lambda x:.5*np.sum((x-y)**2),y,jac=lambda x:x-y,constraints=cons,method='SLSQP',options={'ftol':1e-11,'maxiter':100})
 err=np.linalg.norm(res.x-expected);errors.append(err);check(f'correlated projection {i}',err,1e-7)
for name,psi,slopes in [('shifted',lambda x:(x+.3)**2,(-1.4,2.6)),('exponential',np.exp,(np.exp(-1),np.exp(1)))]:
 X=rng.uniform(-1,1,(128,K));r=encode(X,c,B,2).sum(1);f=(X*X).mean(1)-psi(X.mean(1));n=rng.normal(size=(128,2))*30
 err=abs(decode_gap(r+n,c,B,K,psi)-f);bound=constant(B,K,slopes)*np.linalg.norm(n,axis=1)
 check(name+' correlated uniform bound',max(0,np.max(err-bound)),1e-11)
report={'status':'passed' if all(x['passed'] for x in checks) else 'failed','checks':len(checks),'passing':sum(x['passed'] for x in checks),'observations':len(samples),'max_projection_error':max(errors),'seed':20260913,'executed_utc':datetime.now(timezone.utc).isoformat(),'python':platform.python_version(),'numpy':np.__version__,'scipy':scipy.__version__,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'results':checks,'scope':'Numerical implementation checks, not a universal proof or MSE study.'}
(root/'results/decoder_checks.json').write_text(json.dumps(report,indent=2)+'\n')
(root/'results/decoder_samples.json').write_text(json.dumps(samples)+'\n')
print({k:v for k,v in report.items() if k!='results'})
assert report['status']=='passed'
