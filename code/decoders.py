"""Reusable real-coordinate encoders and sharp strip/rectangle decoders."""
import numpy as np
from scipy.optimize import brentq

def quadratic(M):
 t=M/2; b=2/(1+2*t/(np.sqrt(t*t+2)+t)); return np.sqrt(b*(2-b)),b,-1.

def quartic(M):
 r=brentq(lambda r:8*r*r*(1+r)*(1+3*r)-M*M*(1-3*r),0,1/3,xtol=5e-15)
 d=1+2*r+9*r*r
 return r,np.sqrt(8*r/d),2/((1+r)*np.sqrt(d)),-(1+2*r+3*r*r)/((1+r)*np.sqrt(d))

def encode(s,c,B,p):
 s=np.asarray(s); return np.stack((s,s**p),axis=-1)@np.asarray(B).T+c

def strip_coordinates(y,c,B,K):
 y=np.asarray(y); c=np.asarray(c); B=np.asarray(B)
 v=np.linalg.solve(B,((y-K*c)/K).reshape(-1,2).T).T
 G=B.T@B; m=np.clip(v[:,0],-1,1); t=v[:,1]+G[0,1]/G[1,1]*(v[:,0]-m)
 return np.stack((m,t),axis=-1).reshape(y.shape)

def decode_gap(y,c,B,K,psi,output_range=None):
 v=strip_coordinates(y,c,B,K); result=v[...,1]-psi(v[...,0])
 return result if output_range is None else np.clip(result,*output_range)

def constant(B,K,slopes):
 G=np.asarray(B).T@B; W=np.column_stack((-np.array(slopes),np.ones(2)))
 return np.sqrt(max(w@np.linalg.solve(G,w) for w in W))/K

def decode_mq(y,K,P,a,b):
 y=np.asarray(y)/(K*np.sqrt(P));m=np.clip(y[...,0]/a,-1,1);q=np.clip((y[...,1]+1)/b,0,1)
 return m*q
