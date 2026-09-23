% OLG existence: does capital supply cross the firm's demand, and does the PROVABLE floor cross it?
%   demand (normalised, Aiyagari alpha=9/25, delta=2/25):  alpha/((1-alpha)(r+delta))
%   supply: mean assets per head over a J-period life, cohort born with zero assets
%   provable floor: B_0=0, B_{j+1} = max(0, (1-kap_k)(1 + R B_j) - kap_k h_k),  k = K-j
%     from  c_k <= kap_k (m + H_k(z))  [stageConsumption_le_stageHumanWealth] and Jensen.
function olgexist
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; gam=3; alpha=9/25; delta=2/25;
sd_e=sigma*sqrt(1-rho^2); xg=linspace(-3*sigma,3*sigma,nz); h=xg(2)-xg(1);
Pi=zeros(nz); for i=1:nz, for j=1:nz
  lo=(xg(j)-h/2-rho*xg(i))/sd_e; hi=(xg(j)+h/2-rho*xg(i))/sd_e;
  if j==1, Pi(i,j)=Phi(hi); elseif j==nz, Pi(i,j)=1-Phi(lo); else Pi(i,j)=Phi(hi)-Phi(lo); end
end, end
[V,D]=eig(Pi'); [~,k]=max(abs(diag(D))); nu=abs(V(:,k)); nu=nu/sum(nu); y=exp(xg)'; y=y/(nu'*y);
fprintf('  r      | demand | supply (true) | provable floor | max assets | supply-demand\n');
for r=[-0.04 0 0.02 0.04 0.0417 0.06 0.08 0.10 0.15]
  R=1+r; dem=alpha/((1-alpha)*(r+delta));
  [sup,amax]=olgsupply(R,beta,gam,y,Pi,nu,J);
  flo=provable(R,beta,gam,y,Pi,nu,J);
  fprintf(' %+.4f | %6.3f | %13.4f | %14.4f | %10.1f | %+.3f\n',r,dem,sup,flo,amax,sup-dem);
end
end
function v=Phi(x), v=0.5*erfc(-x/sqrt(2)); end
function [sup,amax]=olgsupply(R,beta,gam,y,Pi,nu,J)
nz=numel(y); na=1200; ag=[0; exp(linspace(log(1e-3),log(4000),na-1))'];
c=egm(R,beta,gam,y,Pi,ag,J); m=y'+R*ag;
mu=zeros(na,nz); mu(1,:)=nu';           % born with zero assets, z ~ stationary
tot=0; amax=0;
for j=0:J-1
  tot=tot+sum(mu,2)'*ag; amax=max(amax,max(ag(sum(mu,2)>1e-14)));
  if j==J-1, break; end
  k=J-1-j; ap=m-c{k+1};                  % saving at stage k
  new=zeros(na,nz);
  for z=1:nz
    w=mu(:,z); idx=w>1e-16; if ~any(idx), continue; end
    x=min(max(ap(:,z),ag(1)),ag(end));
    lo=zeros(na,1); hi=lo; wt=lo;
    [~,bin]=histc(x,ag); bin=max(min(bin,na-1),1);
    frac=(x-ag(bin))./(ag(bin+1)-ag(bin));
    for i=find(idx)'
      b=bin(i); f=frac(i);
      new(b,:)=new(b,:)+w(i)*(1-f)*Pi(z,:);
      new(b+1,:)=new(b+1,:)+w(i)*f*Pi(z,:);
    end
  end
  mu=new;
end
sup=tot/J;
end
function flo=provable(R,beta,gam,y,Pi,nu,J)
nz=numel(y); Th=(beta*R)^(1/gam);
kap=zeros(J,1); kap(1)=1; for k=1:J-1, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
H=zeros(nz,J); for k=1:J-1, H(:,k+1)=(Pi*(y+H(:,k)))/R; end
hbar=zeros(J,1); for k=1:J, hbar(k)=nu'*H(:,k); end
B=0; tot=0;
for j=0:J-1
  tot=tot+B; k=J-1-j;
  if j==J-1, break; end
  B=max(0,(1-kap(k+1))*(1+R*B)-kap(k+1)*hbar(k+1));
end
flo=tot/J;
end
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
