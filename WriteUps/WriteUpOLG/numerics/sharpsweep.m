% Where do all the hypotheses of exists_olgEquilibrium_of_sharpBounds hold, and with what cap?
function sharpsweep
beta=0.96; gam=3; J=60; K=J-1; rho=0.9; sigma=0.4; nz=7; alpha=9/25; delta=2/25;
[Pi,y,nu]=tauchen(rho,sigma,nz); D=@(r) alpha/((1-alpha)*(r+delta));
fprintf('LOW end: ceiling vs demand, and the cap the slackness hypothesis needs\n');
fprintf('   r_lo  | demand  | ceiling B* | B range width | cap needed (ymax/(1-R))\n');
for rlo=[-0.079 -0.075 -0.07 -0.065 -0.06 -0.058 -0.055]
  R=1+rlo; B=ceilfp(rlo,beta,gam,J,y,Pi); d=D(rlo);
  fprintf(' %+.4f | %7.3f | %10.2f | %13.3f | %10.1f\n',rlo,d,B,d-B,max(y)/(1-R));
end
fprintf('\nHIGH end: provable floor vs demand, and the cap the reachable bound needs\n');
fprintf('   r_hi  | demand  | provable floor | margin  | reach(K+1)\n');
for rhi=[0.06 0.08 0.09 0.10 0.12 0.15 0.20]
  f=floorval(rhi,beta,gam,J,y,Pi,nu); d=D(rhi);
  R=1+rhi; rc=0; for j=1:K+1, rc=R*rc+max(y); end
  fprintf(' %+.4f | %7.3f | %14.4f | %+7.3f | %.3e\n',rhi,d,f,f-d,rc);
end
% the widest admissible interval, and the cap it needs
lo=-0.0799; hi=-0.001;
for it=1:80, m=(lo+hi)/2; if ceilfp(m,beta,gam,J,y,Pi)<D(m), lo=m; else hi=m; end, end
rl=lo;
a=0.03; b=0.5;
for it=1:80, m=(a+b)/2; if floorval(m,beta,gam,J,y,Pi,nu)>D(m), b=m; else a=m; end, end
rh=b;
R=1+rh; rc=0; for j=1:K+1, rc=R*rc+max(y); end
fprintf('\n widest interval the theorem covers: [%.4f, %.4f]\n',rl,rh);
fprintf(' cap must exceed max( ymax/(1-R_lo)=%.1f , reach(K+1)=%.3e ) = %.3e\n', ...
  max(y)/(1-(1+rl)),rc,max(max(y)/(1-(1+rl)),rc));
end
function B=ceilfp(r,beta,gam,J,y,Pi)
R=1+r; K=J-1; nz=numel(y); if R>=1, B=inf; return; end
Th=(beta*R)^(1/gam); kap=zeros(J,1); kap(1)=1;
for k=1:K, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
H=zeros(nz,J);
for k=1:K
  M=zeros(nz,1);
  for z=1:nz, M(z)=(sum(Pi(z,:)'.*(y+H(:,k)).^(-gam)))^(-1/gam); end
  H(:,k+1)=min(M/R,(1/kap(k+1)-1)*y);
end
B=0;
for it=1:200000
  best=0; for j=1:J, best=max(best,max((1-kap(j))*(y+R*B)-kap(j)*H(:,j))); end
  if abs(best-B)<1e-12, B=best; break; end
  if best>1e9, B=inf; break; end
  B=best;
end
end
function f=floorval(r,beta,gam,J,y,Pi,nu)
R=1+r; K=J-1; nz=numel(y); Th=(beta*R)^(1/gam);
kap=zeros(J,1); kap(1)=1; for k=1:K, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
Hup=zeros(nz,J); for k=1:K, Hup(:,k+1)=(Pi*(y+Hup(:,k)))/R; end
G=1; F=zeros(nz,1);
for k=0:K-1
  Fn=Pi*F+G*((1-kap(k+2))*y-kap(k+2)*Hup(:,k+2)); G=1+G*(1-kap(k+2))*R; F=Fn;
end
f=(nu'*F)/J;
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
