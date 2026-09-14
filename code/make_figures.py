from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from decoders import quadratic,quartic
root=Path(__file__).resolve().parents[1]
plt.rcParams.update({'font.family':'serif','font.size':9,'axes.titlesize':9,'axes.labelsize':9,'legend.fontsize':8,'pdf.fonttype':42})
s=np.linspace(-1,1,1201);theta=np.linspace(0,2*np.pi,601);rho,aq,bq,cq=quartic(4)
cases=[('Variance',2,2,quadratic(2),[-1,0,1]),('Fourth-order Jensen gap',4,4,(aq,bq,cq),[-1,-np.sqrt(rho),np.sqrt(rho),1]),('Moment interaction $mq$',2,1,quadratic(1),[-1,0,1])]
fig,axs=plt.subplots(1,3,figsize=(7.15,2.65),sharex=True,sharey=True)
for j,(ax,(title,p,M,(a,b,c),contacts)) in enumerate(zip(axs,cases)):
 ax.plot(np.cos(theta),np.sin(theta),':',color='.65',lw=.8,label='Peak boundary')
 ba,bb,bc=(2/np.sqrt(5),2/np.sqrt(5),-1/np.sqrt(5)) if p==4 else (1,1,-1)
 ax.plot(ba*s,bb*s**p+bc,'--',color='#bd6630',lw=1.2,label='Baseline (see caption)')
 ax.plot(a*s,b*s**p+c,color='#17638b',lw=1.6,label='Optimal curve')
 z=np.array(contacts);ax.scatter(a*z,b*z**p+c,color='#17638b',edgecolors='white',linewidths=.4,s=19,zorder=4,label='Peak contacts')
 ax.set_aspect('equal');ax.set(xlim=(-1.13,1.13),ylim=(-1.13,1.13),xticks=(-1,0,1),yticks=(-1,0,1),title=f'({chr(97+j)}) '+title,xlabel=r'$\mathrm{Re}\,\mathscr{E}(s)/\sqrt{P}$')
 ax.text(0,.78,rf'$\Lambda_{{\rm sq}}^\star/(K^2P)={1/(M*M/a**2+1/b**2):.6f}$',ha='center',fontsize=8)
 ax.spines[['top','right']].set_visible(False)
axs[0].set_ylabel(r'$\mathrm{Im}\,\mathscr{E}(s)/\sqrt{P}$')
fig.legend(*axs[0].get_legend_handles_labels(),loc='lower center',ncol=4,frameon=False,bbox_to_anchor=(.5,-.01))
fig.subplots_adjust(left=.07,right=.99,top=.88,bottom=.25,wspace=.16)
for ext in ['pdf','png']:fig.savefig(root/'figures'/f'optimal_curves.{ext}',bbox_inches='tight',dpi=220)
plt.close(fig)
beta=np.geomspace(.001,1,400)
fig,ax=plt.subplots(figsize=(3.4,2.55));ax.loglog(beta,beta**2/(1+beta**2),color='#17638b',lw=1.5,label='Exact squared score');ax.loglog(beta,beta**2,'--',color='#bd6630',lw=1,label=r'$\beta^2$ asymptote')
ax.set(xlabel=r'$\beta$',ylabel=r'$\Lambda_{\rm sq}(\mathscr{E}_\beta;mq)/(K^2P)$');ax.grid(which='major',color='.9',lw=.5);ax.legend(frameon=False);fig.tight_layout()
for ext in ['pdf','png']:fig.savefig(root/'figures'/f'conditioning.{ext}',bbox_inches='tight',dpi=220)
print('Figures generated')
