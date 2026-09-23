% An affine CEILING on accumulated assets, mirroring the affine floor exactly:
%   Gu_0=1, Fu_0=0
%   Gu_{k+1} = 1 + Gu_k (1-kap_{k+1}) R
%   Fu_{k+1}(z) = Pi Fu_k + Gu_k [ (1-kap_{k+1}) y_z - kap_{k+1} Hrisk_{k+1}(z) ]
%   cohortAssets_k(a,z) <= Fu_k(z) + Gu_k a,  so capital per head <= nu'Fu_K/(K+1).
% The floor uses the arithmetic H (saving floor); the ceiling uses Hrisk (saving ceiling).
function affceil
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; K=J-1; gam=3; alpha=9/25; delta=2/25;
[Pi,y,nu]=tauchen(rho,sigma,nz);
fprintf('   r    | demand  | invariant B | affine ceiling | true supply | ceiling/truth\n');
for r=[-0.07 -0.06 -0.04 0 0.02 0.0417 0.05]
  [kap,H,Hr]=build(r,beta,gam,y,Pi,J); R=1+r; d=alpha/((1-alpha)*(r+delta));
  B=invfp(kap,Hr,y,R,J); ce=aff(kap,Hr,Pi,nu,y,R,J); tr=sup(r,beta,gam,y,Pi,nu,J);
  fprintf(' %+.4f | %7.3f | %11.2f | %14.4f | %11.4f | %6.2f\n',r,d,B,ce,tr,ce/tr);
end
% highest admissible r_lo under each ceiling
for mode=1:2
  lo=-0.0799; hi=0.20;
  for it=1:60
    m=(lo+hi)/2; [kap,H,Hr]=build(m,beta,gam,y,Pi,J); R=1+m;
    d=alpha/((1-alpha)*(m+delta));
    if mode==1, v=invfp(kap,Hr,y,R,J); else v=aff(kap,Hr,Pi,nu,y,R,J); end
    if v<d, lo=m; else hi=m; end
  end
  names={'invariant level','affine ceiling'};
  fprintf('\n  %-16s : r_lo admissible up to %+.4f',names{mode},lo);
end
fprintf('\n  (true equilibrium at 0.0509 is the absolute limit)\n');
end
function B=invfp(kap,Hr,y,R,J)
if R>=1, B=inf; return; end
B=0;
for it=1:200000
  best=0; for j=1:J, best=max(best,max((1-kap(j))*(y+R*B)-kap(j)*Hr(:,j))); end
  if abs(best-B)<1e-12, B=best; break; end
  if best>1e9, B=inf; break; end
  B=best;
end
end
function f=aff(kap,Hr,Pi,nu,y,R,J)
K=J-1; nz=numel(y); G=1; F=zeros(nz,1);
for k=0:K-1
  Fn=Pi*F + G*((1-kap(k+2))*y - kap(k+2)*Hr(:,k+2)); G=1+G*(1-kap(k+2))*R; F=Fn;
end
f=(nu'*F)/J;
end
function [kap,H,Hr]=build(r,beta,gam,y,Pi,J)
R=1+r; K=J-1; nz=numel(y); Th=(beta*R)^(1/gam);
kap=zeros(J,1); kap(1)=1; for k=1:K, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
H=zeros(nz,J); Hr=zeros(nz,J);
for k=1:K
  H(:,k+1)=(Pi*(y+H(:,k)))/R;
  M=zeros(nz,1);
  for z=1:nz, M(z)=(sum(Pi(z,:)'.*(y+Hr(:,k)).^(-gam)))^(-1/gam); end
  Hr(:,k+1)=min(M/R,(1/kap(k+1)-1)*y);
end
end
function s=sup(r,beta,gam,y,Pi,nu,J)
R=1+r; nz=numel(y); na=800; ag=[0; exp(linspace(log(1e-3),log(500),na-1))'];
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
