% Worst ratio bound/truth over the whole (a,z) grid at several ages, old vs new.
% Also: the ceiling on assets implied by each bound, a' <= m - c_lower, and its fixed point.
function worstgrid
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; gam=3;
for r=[0.04 -0.07 0.10]
  [Pi,y]=tauchen(rho,sigma,nz); R=1+r; Th=(beta*R)^(1/gam); K=J-1;
  kap=zeros(J,1); kap(1)=1; for k=1:K, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
  Hup=zeros(nz,J); for k=1:K, Hup(:,k+1)=(Pi*(y+Hup(:,k)))/R; end
  H=zeros(nz,J);
  for k=1:K
    M=zeros(nz,1);
    for z=1:nz, M(z)=(sum(Pi(z,:)'.*(y+H(:,k)).^(-gam)))^(-1/gam); end
    H(:,k+1)=min(M/R,(1/kap(k+1)-1)*y);
  end
  na=200; ag=[0; exp(linspace(log(1e-3),log(200),na-1))'];
  G=zeros(na,nz,J);
  for k=1:K
    phi=zeros(na,nz); Gn=zeros(na,nz);
    for z=1:nz, phi(:,z)=max(0,(1-kap(k+1))*(y(z)+R*ag)-kap(k+1)*Hup(z,k+1)); end
    for z=1:nz
      Gk=zeros(na,nz);
      for w=1:nz
        Gk(:,w)=interp1(ag,G(:,w,k),min(max(phi(:,z),ag(1)),ag(end)),'linear','extrap');
      end
      Mz=(sum(Pi(z,:).*((y'+Gk).^(-gam)),2)).^(-1/gam);
      Gn(:,z)=min(Mz/R,(1/kap(k+1)-1)*(y(z)+R*ag));
    end
    G(:,:,k+1)=Gn;
  end
  c=egm(R,beta,gam,y,Pi,ag,J);
  wo=inf; wn=inf; vio=0;
  for k=[10 30 59]
    m=y'+R*ag; tr=c{k+1};
    ob=kap(k+1)*(m+repmat(H(:,k+1)',na,1)); nb=kap(k+1)*(m+G(:,:,k+1));
    wo=min(wo,min(ob(:)./tr(:))); wn=min(wn,min(nb(:)./tr(:)));
    vio=vio+sum(nb(:)>tr(:)+1e-9);
  end
  % ceilings: fixed point of a' = (1-kap)(ymax+R a) - kap*Hlow  with Hlow = 0 / H(zmax) / G
  kk=K+1; f0=@(a) (1-kap(kk))*(max(y)+R*a);
  f1=@(a) (1-kap(kk))*(max(y)+R*a)-kap(kk)*H(nz,kk);
  f2=@(a) (1-kap(kk))*(max(y)+R*a)-kap(kk)*interp1(ag,G(:,nz,kk),min(a,ag(end)),'linear','extrap');
  fprintf('r=%+.2f : worst old/truth %.3f, worst new/truth %.3f, new-exceeds-truth %d\n',r,wo,wn,vio);
  if R<1
    fprintf('        ceilings (fixed points): feasibility %.2f, old %.2f, new %.2f\n', ...
      fp(f0,ag(end)),fp(f1,ag(end)),fp(f2,ag(end)));
  end
end
end
function x=fp(f,hi)
x=0; for i=1:20000, xn=f(x); if xn<=x+1e-12, x=xn; break; end, if xn>hi, x=hi; break; end, x=xn; end
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
