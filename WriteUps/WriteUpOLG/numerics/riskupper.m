% Sharper UPPER bound on consumption: the Euler step produces the power mean with exponent -gamma,
% and the current proof relaxes it to the arithmetic mean by Jensen. Keep the power mean:
%   Ht_0 = 0,  Ht_{k+1}(z) = M^z_{-gam}(y_w + Ht_k(w)) / R      (no cap: this is an upper bound)
%   c_k <= kap_k (m + Ht_k(z))   and so   g_k >= (1-kap_k)(y_z+Ra) - kap_k Ht_k(z).
function riskupper
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; K=J-1; gam=3; alpha=9/25; delta=2/25;
[Pi,y,nu]=tauchen(rho,sigma,nz);
% validity check at r=0.08: is kap_k (m + Ht_k) >= c_k everywhere?
r=0.08; [kap,H,Ht]=build(r,beta,gam,y,Pi,J);
na=400; ag=[0; exp(linspace(log(1e-3),log(300),na-1))'];
R=1+r; c=egm(R,beta,gam,y,Pi,ag,J); m=y'+R*ag; w=inf;
for k=0:K
  b=kap(k+1)*(m+repmat(Ht(:,k+1)',na,1)); w=min(w,min(b(:)-c{k+1}(:)));
end
fprintf('r=%.2f : min over grid of  kap_k(m+Ht_k) - c_k = %+.3e  (>=0 means valid)\n',r,w);
fprintf('        mean human wealth: arithmetic %.2f, power mean %.2f (%.1f%% lower)\n\n', ...
  nu'*H(:,J),nu'*Ht(:,J),100*(1-(nu'*Ht(:,J))/(nu'*H(:,J))));
fprintf('   r    | demand |  floor (arithmetic) | floor (power mean) | gain | true supply\n');
for r=[0.05 0.055 0.06 0.065 0.07 0.08 0.10]
  [kap,H,Ht]=build(r,beta,gam,y,Pi,J); R=1+r; d=alpha/((1-alpha)*(r+delta));
  f1=flr(kap,H,Pi,nu,y,R,J); f2=flr(kap,Ht,Pi,nu,y,R,J);
  fprintf(' %+.3f | %6.3f | %19.4f | %18.4f | %5.2fx | %s\n',r,d,f1,f2,f2/max(f1,1e-9),'-');
end
% new r_hi
a=0.02; b=0.5;
for it=1:80
  mm=(a+b)/2; [kap,H,Ht]=build(mm,beta,gam,y,Pi,J);
  if flr(kap,Ht,Pi,nu,y,1+mm,J) > alpha/((1-alpha)*(mm+delta)), b=mm; else a=mm; end
end
R=1+b; rc=0; for j=1:K+1, rc=R*rc+max(y); end
fprintf('\n r_hi falls from 8.38%% to %.2f%%;  reach(K+1) there = %.3e\n',100*b,rc);
end
function [kap,H,Ht]=build(r,beta,gam,y,Pi,J)
R=1+r; K=J-1; nz=numel(y); Th=(beta*R)^(1/gam);
kap=zeros(J,1); kap(1)=1; for k=1:K, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
H=zeros(nz,J); Ht=zeros(nz,J);
for k=1:K
  H(:,k+1)=(Pi*(y+H(:,k)))/R;
  M=zeros(nz,1);
  for z=1:nz, M(z)=(sum(Pi(z,:)'.*(y+Ht(:,k)).^(-gam)))^(-1/gam); end
  Ht(:,k+1)=M/R;
end
end
function f=flr(kap,H,Pi,nu,y,R,J)
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
