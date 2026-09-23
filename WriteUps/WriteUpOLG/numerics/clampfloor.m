% The floor made asset-dependent, with the saving floor clamped at zero:
%   Phi_k(a,z) = max(0, (1-kap_k)(y_z+Ra) - kap_k H_k(z))       [already `assetFloor` in Lean]
%   Lam_0(z,a) = a
%   Lam_{k+1}(z,a) = a + sum_z' pi(z,z') Lam_k(z', Phi_{k+1}(a,z))
%   capital per head >= sum_z nu_z Lam_K(z,0) / (K+1)
% The affine version is the same thing without the clamp, so it must be at least as good.
function clampfloor
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; K=J-1; gam=3; alpha=9/25; delta=2/25;
[Pi,y,nu]=tauchen(rho,sigma,nz); D=@(r) alpha/((1-alpha)*(r+delta));
fprintf('   r    | demand |  affine floor | clamped floor | true supply | clamped/truth\n');
for r=[0.05 0.06 0.07 0.08 0.10]
  R=1+r; Th=(beta*R)^(1/gam);
  kap=zeros(J,1); kap(1)=1; for k=1:K, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
  H=zeros(nz,J); for k=1:K, H(:,k+1)=(Pi*(y+H(:,k)))/R; end
  fa=aff(kap,H,Pi,nu,y,R,J);
  fc=clamped(kap,H,Pi,nu,y,R,J);
  tr=sup(r,beta,gam,y,Pi,nu,J);
  fprintf(' %+.3f | %6.3f | %13.4f | %13.4f | %11.4f | %6.3f\n',r,D(r),fa,fc,tr,fc/tr);
end
% new r_hi
a=0.02; b=0.30;
for it=1:60
  m=(a+b)/2; R=1+m; Th=(beta*R)^(1/gam);
  kap=zeros(J,1); kap(1)=1; for k=1:K, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
  H=zeros(nz,J); for k=1:K, H(:,k+1)=(Pi*(y+H(:,k)))/R; end
  if clamped(kap,H,Pi,nu,y,R,J) > D(m), b=m; else a=m; end
end
fprintf('\n r_hi falls from 8.38%% to %.2f%%  (absolute limit 5.09%%)\n',100*b);
end
function f=clamped(kap,H,Pi,nu,y,R,J)
K=J-1; nz=numel(y); na=400; ag=[0; exp(linspace(log(1e-4),log(2000),na-1))'];
L=repmat(ag,1,nz);                      % Lam_0(z,a) = a
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
