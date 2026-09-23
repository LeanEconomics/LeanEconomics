% Variant 4: keep the AFFINE ceiling but use assetHumanWealth read at a = 0.
% That is monotone in assets by construction (the human wealth term is a constant), and valid
% because assetHumanWealth rises with assets, so its value at 0 gives the weaker saving ceiling.
% Also check whether the full asset-dependent saving ceiling is monotone in a at all.
function ceilvar
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; K=J-1; gam=3; alpha=9/25; delta=2/25;
[Pi,y,nu]=tauchen(rho,sigma,nz); D=@(r) alpha/((1-alpha)*(r+delta));
na=300; ag=[0; exp(linspace(log(1e-4),log(600),na-1))'];
fprintf('   r    | demand | affine+risk | affine+asset(0) | at-assets+asset | truth\n');
for r=[0.00 0.02 0.03 0.035 0.04]
  R=1+r; Th=(beta*R)^(1/gam);
  kap=zeros(J,1); kap(1)=1; for k=1:K, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
  Hr=riskH(kap,Pi,y,R,gam,J); Hup=arithH(Pi,y,R,J);
  Ga=assetH(kap,Hup,Pi,y,R,gam,J,ag);
  H0=squeeze(Ga(1,:,:));                       % assetHumanWealth at a = 0
  v1=aff(kap,Hr,Pi,nu,y,R,J); v4=aff(kap,H0,Pi,nu,y,R,J);
  v3=atassets(kap,Ga,Pi,nu,y,R,J,ag);
  fprintf(' %+.3f | %6.3f | %11.4f | %15.4f | %15.4f | %6.4f\n',r,D(r),v1,v4,v3,sup(r,beta,gam,y,Pi,nu,J));
end
% monotonicity of the full asset-dependent saving ceiling
r=0.03; R=1+r; Th=(beta*R)^(1/gam);
kap=zeros(J,1); kap(1)=1; for k=1:K, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
Hup=arithH(Pi,y,R,J); Ga=assetH(kap,Hup,Pi,y,R,gam,J,ag);
bad=0; mn=inf;
for k=1:K
  for z=1:nz
    Ab=max(0,(1-kap(k+1))*(y(z)+R*ag)-kap(k+1)*Ga(:,z,k+1));
    d=diff(Ab); mn=min(mn,min(d)); bad=bad+sum(d<-1e-12);
  end
end
fprintf('\n saving ceiling monotone in a at r=0.03? decreasing steps: %d, min step %+.3e\n',bad,mn);
% new r_lo for variant 4
lo=-0.0799; hi=0.0509;
for it=1:50
  m=(lo+hi)/2; R=1+m; Th=(beta*R)^(1/gam);
  kap=zeros(J,1); kap(1)=1; for k=1:K, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
  Hup=arithH(Pi,y,R,J); Ga=assetH(kap,Hup,Pi,y,R,gam,J,ag); H0=squeeze(Ga(1,:,:));
  if aff(kap,H0,Pi,nu,y,R,J)<D(m), lo=m; else hi=m; end
end
fprintf(' affine + assetHumanWealth(0) : r_lo admissible up to %+.4f  (risk gave +0.0278)\n',lo);
end
function v=atassets(kap,Ga,Pi,nu,y,R,J,ag)
K=J-1; nz=numel(y); na=numel(ag); X=repmat(ag,1,nz);
for k=0:K-1
  Ab=zeros(na,nz);
  for z=1:nz, Ab(:,z)=max(0,(1-kap(k+2))*(y(z)+R*ag)-kap(k+2)*Ga(:,z,k+2)); end
  Xn=zeros(na,nz);
  for z=1:nz
    acc=zeros(na,1);
    for w=1:nz
      acc=acc+Pi(z,w)*interp1(ag,X(:,w),min(max(Ab(:,z),ag(1)),ag(end)),'linear','extrap');
    end
    Xn(:,z)=ag+acc;
  end
  X=Xn;
end
v=(nu'*X(1,:)')/J;
end
function Ga=assetH(kap,Hup,Pi,y,R,gam,J,ag)
K=J-1; nz=numel(y); na=numel(ag); Ga=zeros(na,nz,J);
for k=0:K-1
  ph=zeros(na,nz);
  for z=1:nz, ph(:,z)=max(0,(1-kap(k+2))*(y(z)+R*ag)-kap(k+2)*Hup(z,k+2)); end
  Gn=zeros(na,nz);
  for z=1:nz
    Gk=zeros(na,nz);
    for w=1:nz
      Gk(:,w)=interp1(ag,Ga(:,w,k+1),min(max(ph(:,z),ag(1)),ag(end)),'linear','extrap');
    end
    Mz=(sum(Pi(z,:).*((y'+Gk).^(-gam)),2)).^(-1/gam);
    Gn(:,z)=min(Mz/R,(1/kap(k+2)-1)*(y(z)+R*ag));
  end
  Ga(:,:,k+2)=Gn;
end
end
function Hr=riskH(kap,Pi,y,R,gam,J)
K=J-1; nz=numel(y); Hr=zeros(nz,J);
for k=1:K
  M=zeros(nz,1);
  for z=1:nz, M(z)=(sum(Pi(z,:)'.*(y+Hr(:,k)).^(-gam)))^(-1/gam); end
  Hr(:,k+1)=min(M/R,(1/kap(k+1)-1)*y);
end
end
function H=arithH(Pi,y,R,J)
nz=numel(y); H=zeros(nz,J); for k=1:J-1, H(:,k+1)=(Pi*(y+H(:,k)))/R; end
end
function f=aff(kap,H,Pi,nu,y,R,J)
K=J-1; nz=numel(y); G=1; F=zeros(nz,1);
for k=0:K-1
  Fn=Pi*F + G*((1-kap(k+2))*y - kap(k+2)*H(:,k+2)); G=1+G*(1-kap(k+2))*R; F=Fn;
end
f=(nu'*F)/J;
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
