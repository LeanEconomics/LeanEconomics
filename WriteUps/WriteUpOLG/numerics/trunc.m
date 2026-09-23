% The truncated-horizon upper bound on consumption:  c_k <= kap_j (m + H_j(z))  for every j <= k,
% got by feeding the trivial bound c <= m into the same Euler step j times instead of k times.
% (1) is it valid?  (2) what does the max over j do to the aggregate saving floor?
function trunc
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; K=J-1; gam=3; alpha=9/25; delta=2/25;
[Pi,y,nu]=tauchen(rho,sigma,nz);
% (1) validity at r = 0.08
r=0.08; R=1+r; Th=(beta*R)^(1/gam);
kap=zeros(J,1); kap(1)=1; for k=1:K, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
H=zeros(nz,J); for k=1:K, H(:,k+1)=(Pi*(y+H(:,k)))/R; end
na=400; ag=[0; exp(linspace(log(1e-3),log(300),na-1))'];
c=egm(R,beta,gam,y,Pi,ag,J); m=y'+R*ag;
worst=inf;
for k=0:K
  for j=0:k
    b=kap(j+1)*(m+repmat(H(:,j+1)',na,1));
    worst=min(worst,min(b(:)-c{k+1}(:)));
  end
end
fprintf('r=%.2f : min over all k,j<=k and all states of  kap_j(m+H_j) - c_k  =  %+.3e\n',r,worst);
fprintf('        (nonnegative means every truncated bound is valid)\n\n');
% (2) aggregate floor with the horizon truncated at J0
fprintf('   r    | demand |  floor J0=K (current) | best truncated floor | best J0 | true supply\n');
for r=[0.05 0.06 0.07 0.08 0.09 0.10]
  R=1+r; Th=(beta*R)^(1/gam); d=alpha/((1-alpha)*(r+delta));
  kap=zeros(J,1); kap(1)=1; for k=1:K, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
  H=zeros(nz,J); for k=1:K, H(:,k+1)=(Pi*(y+H(:,k)))/R; end
  base=flr(K,kap,H,Pi,nu,y,R,J); best=-inf; bj=0;
  for J0=1:K
    v=flr(J0,kap,H,Pi,nu,y,R,J); if v>best, best=v; bj=J0; end
  end
  fprintf(' %+.3f | %6.3f | %21.4f | %20.4f | %7d | %s\n',r,d,base,best,bj,'-');
end
end
function f=flr(J0,kap,H,Pi,nu,y,R,J)
% F_{k+1}(z) = Pi F_k + G_k[(1-kap_j)y_z - kap_j H_j(z)],  j = min(k+1,J0)
K=J-1; nz=numel(y); G=1; F=zeros(nz,1);
for k=0:K-1
  j=min(k+1,J0);
  Fn=Pi*F + G*((1-kap(j+1))*y - kap(j+1)*H(:,j+1));
  G=1+G*(1-kap(j+1))*R; F=Fn;
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
