% How much slack is there for a bound on the RISK CORRECTION to the certainty-equivalent criterion?
%   Theorem 1 at (a=0, z_max) needs  dg/dr >= 0  for the risky household.
%   The CE household (deterministic, unconstrained, conditional mean income path from z_max) has
%   dg_CE/dr in closed form, and is proved antitone for gamma <= 1 and by the chord above.
%   Write  dg/dr = dg_CE/dr - corr.   Then Theorem 1 follows from any bound B >= corr with
%   dg_CE/dr >= B.  The allowed slack factor is dg_CE/dr divided by corr.
function riskgap
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60;
[Pi,y,nu]=tauchen(rho,sigma,nz);
e=zeros(nz,1); e(nz)=1; ypath=zeros(J,1); v=e;
for t=1:J, ypath(t)=v'*y; v=Pi'*v; end
ag=[0; exp(linspace(log(1e-4),log(600),2999))'];
r=0.04; dr=1e-3;
fprintf(' gamma | dg_CE/dr | dg_risk/dr |   corr   | slack factor | verdict for Thm 1\n');
for gam=[1 2 2.5 3 3.2 3.39 4 4.33 5]
  g0=detg(1+r,beta,gam,ypath); g1=detg(1+r+dr,beta,gam,ypath); dce=(g1-g0)/dr;
  c=egm(1+r,beta,gam,y,Pi,ag,J);      gr0=y(nz)-c{J}(1,nz);
  c=egm(1+r+dr,beta,gam,y,Pi,ag,J);   gr1=y(nz)-c{J}(1,nz);
  drk=(gr1-gr0)/dr;
  corr=dce-drk;
  if corr>0, sl=dce/corr; else, sl=inf; end
  if drk>=0, vd='holds'; else, vd='FAILS'; end
  fprintf(' %5.2f | %8.3f | %10.3f | %8.3f | %12.3f | %s\n',gam,dce,drk,corr,sl,vd);
end
fprintf('\n corr as a fraction of dg_CE/dr is what a bound must beat; a bound loose by more\n');
fprintf(' than the slack factor cannot certify Theorem 1 at that gamma.\n');
end
function g0=detg(R,beta,gam,ypath)
J=numel(ypath); t=(0:J-1)';
W=sum(ypath.*R.^(-t)); D=sum(beta.^(t/gam).*R.^(t/gam-t));
g0=ypath(1)-W/D;
end
function c=egm(R,beta,gamma,y,Pi,ag,J)
nz=numel(y); na=numel(ag); m=y'+R*ag; c=cell(J,1); c{1}=m;
for k=1:J-1
  up=c{k}.^(-gamma); rhs=beta*R*(up*Pi'); cend=rhs.^(-1/gamma); mend=cend+ag; cn=zeros(na,nz);
  for z=1:nz
    cn(:,z)=interp1(mend(:,z),cend(:,z),m(:,z),'linear','extrap');
    corner=m(:,z)<mend(1,z); cn(corner,z)=m(corner,z);
  end
  c{k+1}=min(cn,m);
end
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
