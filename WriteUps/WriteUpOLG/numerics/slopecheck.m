% Single crossing WITHOUT monotone supply: does capital supply ever fall FASTER than demand?
%   clearing (wage units):  S(r) = D(r) = alpha/((1-alpha)(r+delta))
%   single crossing needs, for every r1 < r2 in the bracket,
%       S(r2) - S(r1)  >  D(r2) - D(r1)        (supply may bend back, just not that fast)
%   provable from the EXISTING bracket F(r) <= S(r) <= C(r) via the stronger
%       F(r2) - C(r1)  >  D(r2) - D(r1)
%   F = clamped floor (le_olgCapital_at), C = affine ceiling (olgCapital_le_cohortCeil).
function slopecheck
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; alpha=9/25; delta=2/25;
[Pi,y,nu]=tauchen(rho,sigma,nz);
D=@(r) alpha/((1-alpha)*(r+delta));
rg=0.02:0.005:0.08; n=numel(rg); na=1200; ag=[0; exp(linspace(log(1e-3),log(4000),na-1))'];
fprintf('bracket r in [%.2f, %.2f], %d points, %d pairs;  lambda = %.4f\n\n',...
        rg(1),rg(end),n,n*(n-1)/2,1/beta-1);
for gam=[1 2 3 5 8 12]
  S=zeros(n,1); F=zeros(n,1); C=zeros(n,1); Dv=arrayfun(D,rg)';
  for i=1:n
    r=rg(i); R=1+r; Th=(beta*R)^(1/gam);
    kap=zeros(J,1); kap(1)=1; for k=1:J-1, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
    Hup=zeros(nz,J); for k=1:J-1, Hup(:,k+1)=(Pi*(y+Hup(:,k)))/R; end
    Hr=riskH(kap,Pi,y,R,gam,J);
    S(i)=sup(R,beta,gam,y,Pi,nu,J,ag);
    F(i)=clamped(kap,Hup,Pi,nu,y,R,J);
    C(i)=aff(kap,Hr,Pi,nu,y,R,J);
  end
  % worst secant slopes
  mS=inf; mSD=inf; mBR=-inf; wS=[0 0]; wB=[0 0]; mBRv=inf;
  for i=1:n, for k=i+1:n
    h=rg(k)-rg(i);
    sS=(S(k)-S(i))/h; sD=(Dv(k)-Dv(i))/h;
    if sS<mS, mS=sS; wS=[rg(i) rg(k)]; end
    mSD=min(mSD,sS-sD);
    sB=(F(k)-C(i))/h;
    if sB-sD<mBRv, mBRv=sB-sD; wB=[rg(i) rg(k)]; end
  end, end
  dec=sum(diff(S)<0);
  fprintf('gamma=%2g : r* in bracket, S ranges %.3f..%.3f, D ranges %.3f..%.3f\n',...
          gam,min(S),max(S),min(Dv),max(Dv));
  fprintf('          adjacent steps with S falling: %d of %d\n',dec,n-1);
  fprintf('          worst secant slope of S      : %+9.3f  (on [%.3f,%.3f])\n',mS,wS(1),wS(2));
  fprintf('          demand secant slope there    : %+9.3f\n',(D(wS(2))-D(wS(1)))/(wS(2)-wS(1)));
  fprintf('          TRUE margin  min(sS - sD)    : %+9.3f   %s\n',mSD,verdict(mSD));
  fprintf('          BRACKET margin min(sB - sD)  : %+9.3f   %s  (on [%.3f,%.3f])\n\n',...
          mBRv,verdict(mBRv),wB(1),wB(2));
end
end
function s=verdict(v), if v>0, s='PASS'; else, s='fail'; end, end
function S=sup(R,beta,gam,y,Pi,nu,J,ag)
nz=numel(y); na=numel(ag); c=egm(R,beta,gam,y,Pi,ag,J); m=y'+R*ag;
mu=zeros(na,nz); mu(1,:)=nu'; tot=0;
for j=0:J-1
  k=J-1-j; ap=max(m-c{k+1},0); tot=tot+sum(mu,2)'*ag;
  if j==J-1, break; end
  new=zeros(na,nz);
  for z=1:nz
    w=mu(:,z); x=min(max(ap(:,z),ag(1)),ag(end));
    bin=discretize(x,ag); bin(isnan(bin))=na-1; bin=max(min(bin,na-1),1);
    frac=(x-ag(bin))./(ag(bin+1)-ag(bin));
    new=new+accumarray([bin;bin+1],[w.*(1-frac);w.*frac],[na 1])*Pi(z,:);
  end
  mu=new;
end
S=tot/J;
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
