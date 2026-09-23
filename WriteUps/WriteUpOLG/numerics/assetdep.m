% Asset-dependent constraint-incidence bound.
%  current:  H_{k+1}(z) = min( M^z_{-g}(y_w+H_k(w))/R , (1/kap_{k+1}-1) y_z )
%  new:      G_{k+1}(z,a) = min( M^z_{-g}(y_w+G_k(w,phi))/R , (1/kap_{k+1}-1)(y_z+R a) )
%            phi_{k+1}(a,z) = max(0,(1-kap_{k+1})(y_z+R a) - kap_{k+1} Hup_{k+1}(z))   [saving floor]
%  bound on consumption: kap_k (m + H_k) <= c_k, likewise with G.
function assetdep
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; gam=3; r=0.04;
[Pi,y]=tauchen(rho,sigma,nz); R=1+r; Th=(beta*R)^(1/gam); K=J-1;
kap=zeros(J,1); kap(1)=1; for k=1:K, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
Hup=zeros(nz,J); for k=1:K, Hup(:,k+1)=(Pi*(y+Hup(:,k)))/R; end     % stageHumanWealth
% current (asset-free) risk human wealth
H=zeros(nz,J);
for k=1:K
  M=zeros(nz,1);
  for z=1:nz, M(z)=(sum(Pi(z,:)'.*(y+H(:,k)).^(-gam)))^(-1/gam); end
  H(:,k+1)=min(M/R,(1/kap(k+1)-1)*y);
end
% new (asset-dependent)
na=200; ag=[0; exp(linspace(log(1e-3),log(200),na-1))'];
G=zeros(na,nz,J);
for k=1:K
  phi=zeros(na,nz); Gn=zeros(na,nz);
  for z=1:nz
    m=y(z)+R*ag;
    phi(:,z)=max(0,(1-kap(k+1))*m-kap(k+1)*Hup(z,k+1));
  end
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
% truth
c=egm(R,beta,gam,y,Pi,ag,J);
fprintf('r=%.2f gamma=%g  J=%d.  Bound / truth at stage k=%d (first period of life)\n',r,gam,J,K);
fprintf('   a    |   z    |  truth   | old bound | new bound | old/truth | new/truth\n');
for ai=[1 20 60 100 140]
  for z=[1 4 7]
    a=ag(ai); m=y(z)+R*a; tr=c{J}(ai,z);
    ob=kap(J)*(m+H(z,J)); nb=kap(J)*(m+G(ai,z,J));
    fprintf(' %6.2f | %6.3f | %8.4f | %9.4f | %9.4f | %9.3f | %9.3f\n', ...
      a,y(z),tr,ob,nb,ob/tr,nb/tr);
  end
end
fprintf('\n cap binding (old) at k=%d: ',K); disp((H(:,J)'<(1./kap(J)-1).*y'-1e-10));
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
