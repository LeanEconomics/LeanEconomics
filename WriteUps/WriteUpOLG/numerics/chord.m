% A SUFFICIENT criterion for the certainty-equivalent household, valid for every gamma.
% The exact criterion is  U <= sum_t v_t (lam^t)^theta.  Since x^theta is concave and every
% lam^t lies in [m, 1] with m = lam^{J-1}, it lies above its chord there, so
%      sum_t v_t (lam^t)^theta  >=  chord(V),   chord(x) = m^th + (1-m^th)(x-m)/(1-m).
% Sufficient condition:  U <= chord(V).  Compare its threshold with the exact one.
function chord
beta=0.96; J=60; rho=0.9; sigma=0.4; nz=7;
[Pi,y,~]=tauchen(rho,sigma,nz);
yce=zeros(J,1); d=zeros(1,nz); d(nz)=1;
for t=1:J, yce(t)=d*y; d=d*Pi; end
yflat=ones(J,1);
fprintf('  path   |  r   |   dR   | exact gamma* | chord gamma* | Jensen(necess) | cost\n');
for r=[0.02 0.04 0.06]
  for dR=[1e-5 1e-3 1e-2]
    ge=bisect(@(g) exact(g,r,beta,J,yce,dR),0.3,60);
    gc=bisect(@(g) chordc(g,r,beta,J,yce,dR),0.3,60);
    gj=bisect(@(g) jens(g,r,beta,J,yce,dR),0.3,60);
    fprintf(' CE top | %.2f | %.0e | %12.4f | %12.4f | %14.4f | %.4f\n',r,dR,ge,gc,gj,ge-gc);
  end
end
fprintf('\n flat income, r = 0.06, dR = 1e-3: exact %.3f, chord %.3f\n', ...
  bisect(@(g) exact(g,0.06,beta,J,yflat,1e-3),0.3,200), ...
  bisect(@(g) chordc(g,0.06,beta,J,yflat,1e-3),0.3,200));
end
function [U,V,lam,th]=parts(gam,r,beta,J,y,dR)
R1=1+r; R2=R1+dR; lam=R1/R2; th=1-1/gam; t=(0:J-1)';
u=y.*R1.^(-t); u=u/sum(u);
w=beta.^(t/gam).*R1.^(t/gam-t); w=w/sum(w);
U=sum(u.*lam.^t); V=sum(w.*lam.^t);
end
function v=exact(gam,r,beta,J,y,dR)
R1=1+r; R2=R1+dR; t=(0:J-1)';
W1=sum(y.*R1.^(-t)); W2=sum(y.*R2.^(-t));
D1=sum(beta.^(t/gam).*R1.^(t/gam-t)); D2=sum(beta.^(t/gam).*R2.^(t/gam-t));
v=W1*D2-W2*D1;
end
function v=chordc(gam,r,beta,J,y,dR)
[U,V,lam,th]=parts(gam,r,beta,J,y,dR);
if th<=0, v=1; return; end
m=lam^(J-1); ch=m^th+(1-m^th)*(V-m)/(1-m);
v=ch-U;
end
function v=jens(gam,r,beta,J,y,dR)
[U,V,~,th]=parts(gam,r,beta,J,y,dR);
if th<=0, v=1; return; end
v=V^th-U;
end
function x=bisect(f,lo,hi)
if f(hi)>0, x=hi; return; end
if f(lo)<0, x=lo; return; end
for it=1:200, m=(lo+hi)/2; if f(m)>0, lo=m; else hi=m; end, end
x=lo;
end
function [Pi,y,nu]=tauchen(rho,sigma,nz)
sd=sigma*sqrt(1-rho^2); xg=linspace(-3*sigma,3*sigma,nz); h=xg(2)-xg(1);
Pi=zeros(nz); for i=1:nz, for j=1:nz
  lo=(xg(j)-h/2-rho*xg(i))/sd; hi=(xg(j)+h/2-rho*xg(i))/sd;
  if j==1, Pi(i,j)=Phi(hi); elseif j==nz, Pi(i,j)=1-Phi(lo); else Pi(i,j)=Phi(hi)-Phi(lo); end
end, end
[V,Dg]=eig(Pi'); [~,k]=max(abs(diag(Dg))); nu=abs(V(:,k)); nu=nu/sum(nu);
y=exp(xg)'; y=y/(nu'*y);
end
function v=Phi(x), v=0.5*erfc(-x/sqrt(2)); end
