% Check EVERY hypothesis of exists_olgEquilibrium_of_sharpBounds at one calibration,
% exactly as the Lean statement writes them, and report each margin.
function sharpcheck
beta=0.96; gam=3; J=60; K=J-1; rho=0.9; sigma=0.4; nz=7;
alpha=9/25; delta=2/25;
rlo=-0.07; rhi=0.10; acap=1e4; B=30;
[Pi,y,nu]=tauchen(rho,sigma,nz);
D=@(r) alpha/((1-alpha)*(r+delta));
fprintf('calibration: beta=%.2f gamma=%g J=%d  Tauchen(rho=%.1f,sigma=%.1f,%d)\n',beta,gam,J,rho,sigma,nz);
fprintf('             alpha=9/25 delta=2/25, D(r)=alpha/((1-alpha)(r+delta))\n');
fprintf('             r_lo=%+.2f  r_hi=%+.2f  assetCap=%.0e  B=%g\n\n',rlo,rhi,acap,B);
ok=true;
% --- rates admissible, interval, demand continuous
p('0 < 1+r_lo', 1+rlo, 0); p('0 < 1+r_hi', 1+rhi, 0); p('r_lo <= r_hi', rhi-rlo, 0);
p('r_lo + delta > 0 (D continuous)', rlo+delta, 0);
% --- weights
p('sum nu = 1 (error)', 1e-12-abs(sum(nu)-1), 0); p('min nu', min(nu), 0);
% --- LOW END --------------------------------------------------------------
Rl=1+rlo; Thl=(beta*Rl)^(1/gam);
kapl=zeros(J,1); kapl(1)=1; for k=1:K, kapl(k+1)=kapl(k)*Rl/(Thl+kapl(k)*Rl); end
Hl=zeros(nz,J);
for k=1:K
  M=zeros(nz,1);
  for z=1:nz, M(z)=(sum(Pi(z,:)'.*(y+Hl(:,k)).^(-gam)))^(-1/gam); end
  Hl(:,k+1)=min(M/Rl,(1/kapl(k+1)-1)*y);
end
p('hslo: assetCap - (ymax + R_lo*assetCap)', acap-(max(y)+Rl*acap), 0);
p('hB0: B >= 0', B, 0); p('hBcap: assetCap - B', acap-B, 0);
worst=-inf;
for j=1:J, worst=max(worst,max((1-kapl(j))*(y+Rl*B)-kapl(j)*Hl(:,j))); end
p('hinv: B - max_{j,w}(...)', B-worst, 0);
p('hBD: D(r_lo) - B', D(rlo)-B, 0);
% --- HIGH END -------------------------------------------------------------
Rh=1+rhi; Thh=(beta*Rh)^(1/gam);
kaph=zeros(J,1); kaph(1)=1; for k=1:K, kaph(k+1)=kaph(k)*Rh/(Thh+kaph(k)*Rh); end
Hup=zeros(nz,J); for k=1:K, Hup(:,k+1)=(Pi*(y+Hup(:,k)))/Rh; end
rch=0; for j=1:K+1, rch=Rh*rch+max(y); end
p('hcap: assetCap - reach(K+1)', acap-rch, 0);
G=1; F=zeros(nz,1);
for k=0:K-1
  Fn=Pi*F + G*((1-kaph(k+2))*y - kaph(k+2)*Hup(:,k+2));
  G=1+G*(1-kaph(k+2))*Rh; F=Fn;
end
flo=(nu'*F)/J;
p('hDfloor: floor - D(r_hi)', flo-D(rhi), 0);
fprintf('\n  key constants: reach(K+1)=%.1f, ceiling fixed point=%.2f, floor=%.4f, D(r_lo)=%.3f, D(r_hi)=%.3f\n', ...
  rch,worst,flo,D(rlo),D(rhi));
% --- the conclusion: where does supply actually cross demand?
lo=rlo; hi=rhi;
for it=1:40
  m=(lo+hi)/2; if sup(m,beta,gam,y,Pi,nu,J)<D(m), lo=m; else hi=m; end
end
fprintf('  conclusion: an equilibrium exists in [%.2f, %.2f]; the true one is at r = %.4f\n',rlo,rhi,hi);
end
function v=p(name,margin,thr)
if margin>thr, s='PASS'; else s='FAIL'; end
fprintf('  %-38s %s   margin %+.4e\n',name,s,margin); v=margin>thr;
end
function s=sup(r,beta,gam,y,Pi,nu,J)
R=1+r; nz=numel(y); na=1200; ag=[0; exp(linspace(log(1e-3),log(4000),na-1))'];
c=egm(R,beta,gam,y,Pi,ag,J); m=y'+R*ag; mu=zeros(na,nz); mu(1,:)=nu'; tot=0;
for j=0:J-1
  tot=tot+sum(mu,2)'*ag; if j==J-1, break; end
  k=J-1-j; ap=m-c{k+1}; new=zeros(na,nz);
  for z=1:nz
    w=mu(:,z); idx=w>1e-16; if ~any(idx), continue; end
    x=min(max(ap(:,z),ag(1)),ag(end)); [~,bin]=histc(x,ag); bin=max(min(bin,na-1),1);
    frac=(x-ag(bin))./(ag(bin+1)-ag(bin));
    for i=find(idx)'
      b=bin(i); f=frac(i);
      new(b,:)=new(b,:)+w(i)*(1-f)*Pi(z,:); new(b+1,:)=new(b+1,:)+w(i)*f*Pi(z,:);
    end
  end
  mu=new;
end
s=tot/J;
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
function c=egm(R,beta,gamma,y,Pi,ag,J)
nz=numel(y); na=numel(ag); m=y'+R*ag; c=cell(J,1); c{1}=m;
for k=1:J-1
  up=c{k}.^(-gamma); rhs=beta*R*(up*Pi'); cend=rhs.^(-1/gamma); mend=cend+ag; cn=zeros(na,nz);
  for z=1:nz
    cn(:,z)=interp1(mend(:,z),cend(:,z),m(:,z),'linear','extrap');
    corner=m(:,z)<mend(1,z); cn(corner,z)=m(corner,z);
  end
  cn=min(cn,m); c{k+1}=cn;
end
end
