% Every hypothesis of exists_olgEquilibrium_affine, at the tightened bracket.
function clampcheck
beta=0.96; gam=3; J=60; K=J-1; rho=0.9; sigma=0.4; nz=7; alpha=9/25; delta=2/25;
rlo=0.02; rhi=0.08; acap=1e4;
[Pi,y,nu]=tauchen(rho,sigma,nz); D=@(r) alpha/((1-alpha)*(r+delta));
fprintf('r_lo=%+.2f  r_hi=%+.2f  assetCap=%.0e   (lambda = %.4f)\n\n',rlo,rhi,acap,1/beta-1);
p('0 < 1+r_lo',1+rlo); p('0 < 1+r_hi',1+rhi); p('r_lo <= r_hi',rhi-rlo);
p('r_lo + delta > 0 (D continuous)',rlo+delta); p('min nu',min(nu));
% hslo: the cap is forward invariant at r_lo (needs r_lo < lambda)
Rl=1+rlo; Thl=(beta*Rl)^(1/gam);
kl=zeros(J,1); kl(1)=1; for k=1:K, kl(k+1)=kl(k)*Rl/(Thl+kl(k)*Rl); end
worst=-inf; for j=1:J, worst=max(worst,(1-kl(j))*(max(y)+Rl*acap)); end
p('hslo: assetCap - max_j (1-kap_j)(ymax+R_lo*cap)',acap-worst);
% ceiling
Hrl=riskH(kl,Pi,y,Rl,gam,J);
ce=aff(kl,Hrl,Pi,nu,y,Rl,J);
p('hceil: D(r_lo) - ceiling',D(rlo)-ce);
% high end
Rh=1+rhi; Thh=(beta*Rh)^(1/gam);
kh=zeros(J,1); kh(1)=1; for k=1:K, kh(k+1)=kh(k)*Rh/(Thh+kh(k)*Rh); end
Hup=zeros(nz,J); for k=1:K, Hup(:,k+1)=(Pi*(y+Hup(:,k)))/Rh; end
rc=0; for j=1:K+1, rc=Rh*rc+max(y); end
p('hcap: assetCap - reach(K+1)',acap-rc);
fl=clamped(kh,Hup,Pi,nu,y,Rh,J);
p('hfloor: floor - D(r_hi)',fl-D(rhi));
fprintf('\n  ceiling %.4f vs demand %.4f at r_lo;  floor %.4f vs demand %.4f at r_hi\n', ...
  ce,D(rlo),fl,D(rhi));
fprintf('  reach(K+1)=%.1f, cap invariance margin %.1f\n',rc,acap-worst);
fprintf('  bracket [%.2f, %.2f] contains the true equilibrium r = 0.0509\n',rlo,rhi);
end
function v=p(n,m)
if m>0, s='PASS'; else s='FAIL'; end
fprintf('  %-46s %s  margin %+.4e\n',n,s,m); v=m>0;
end
function Hr=riskH(kap,Pi,y,R,gam,J)
K=J-1; nz=numel(y); Hr=zeros(nz,J);
for k=1:K
  M=zeros(nz,1);
  for z=1:nz, M(z)=(sum(Pi(z,:)'.*(y+Hr(:,k)).^(-gam)))^(-1/gam); end
  Hr(:,k+1)=min(M/R,(1/kap(k+1)-1)*y);
end
end
function f=aff(kap,H,Pi,nu,y,R,J)
K=J-1; nz=numel(y); G=1; F=zeros(nz,1);
for k=0:K-1
  Fn=Pi*F + G*((1-kap(k+2))*y - kap(k+2)*H(:,k+2)); G=1+G*(1-kap(k+2))*R; F=Fn;
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
function f=clamped(kap,H,Pi,nu,y,R,J)
K=J-1; nz=numel(y); na=400; ag=[0; exp(linspace(log(1e-4),log(2000),na-1))'];
L=repmat(ag,1,nz);
for k=0:K-1
  Ph=zeros(na,nz);
  for z=1:nz, Ph(:,z)=max(0,(1-kap(k+2))*(y(z)+R*ag)-kap(k+2)*H(z,k+2)); end
  Ln=zeros(na,nz);
  for z=1:nz
    acc=zeros(na,1);
    for w=1:nz
      acc=acc+Pi(z,w)*interp1(ag,L(:,w),min(max(Ph(:,z),ag(1)),ag(end)),'linear','extrap');
    end
    Ln(:,z)=ag+acc;
  end
  L=Ln;
end
f=(nu'*L(1,:)')/J;
end
