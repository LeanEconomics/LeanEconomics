% Asset-dependent UPPER bound on consumption keeping the power mean:
%   Abar_{k+1}(a,z) = (1-kap_{k+1})(y_z+Ra) - kap_{k+1} Hrisk_{k+1}(z)   [upper bd on saving]
%   Gam_0(a,z) = y_z + R a
%   Gam_{k+1}(a,z) = min( y_z+Ra , M^z_{-gam}( Gam_k(Abar,w) ) / Thorn )
% The shift by R*Abar sits INSIDE the power mean, so superadditivity is not in the way.
function gamma
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; K=J-1; gam=3; alpha=9/25; delta=2/25;
[Pi,y,nu]=tauchen(rho,sigma,nz);
fprintf('   r    | c bound at birth: arithmetic | power-mean | truth | floor arith | floor new\n');
for r=[0.06 0.08 0.10]
  R=1+r; Th=(beta*R)^(1/gam);
  kap=zeros(J,1); kap(1)=1; for k=1:K, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
  H=zeros(nz,J); for k=1:K, H(:,k+1)=(Pi*(y+H(:,k)))/R; end
  Hr=zeros(nz,J);
  for k=1:K
    M=zeros(nz,1);
    for z=1:nz, M(z)=(sum(Pi(z,:)'.*(y+Hr(:,k)).^(-gam)))^(-1/gam); end
    Hr(:,k+1)=min(M/R,(1/kap(k+1)-1)*y);
  end
  na=300; ag=[0; exp(linspace(log(1e-3),log(400),na-1))'];
  m=y'+R*ag;
  Gam=zeros(na,nz,J); Gam(:,:,1)=m;
  for k=0:K-1
    Ab=zeros(na,nz);
    for z=1:nz, Ab(:,z)=(1-kap(k+2))*m(:,z)-kap(k+2)*Hr(z,k+2); end
    Ab=max(Ab,0); Gn=zeros(na,nz);
    for z=1:nz
      Gk=zeros(na,nz);
      for w=1:nz
        Gk(:,w)=interp1(ag,Gam(:,w,k+1),min(max(Ab(:,z),ag(1)),ag(end)),'linear','extrap');
      end
      Mz=(sum(Pi(z,:).*(Gk.^(-gam)),2)).^(-1/gam);
      Gn(:,z)=min(m(:,z),Mz/Th);
    end
    Gam(:,:,k+2)=Gn;
  end
  % truth and the two bounds at birth (a=0), averaged over z with nu
  c=egm(R,beta,gam,y,Pi,ag,J);
  tr=nu'*c{J}(1,:)'; ba=nu'*(kap(J)*(m(1,:)'+H(:,J))); bn=nu'*Gam(1,:,J)';
  % validity of the new bound over the whole grid
  bad=0; for k=0:K, bad=bad+sum(sum(Gam(:,:,k+1)<c{k+1}-1e-9)); end
  % floors: arithmetic affine vs new (scalar recursion with the new bound at a = B)
  f1=flr(kap,H,Pi,nu,y,R,J);
  B=0; tot=0;
  for j=0:K
    tot=tot+B; if j==K, break; end
    k=K-j; cb=0;
    for z=1:nz
      cb=cb+nu(z)*interp1(ag,Gam(:,z,k+1),min(max(B,ag(1)),ag(end)),'linear','extrap');
    end
    B=max(0,1+R*B-cb);
  end
  f2=tot/J;
  fprintf(' %+.3f | %28.4f | %10.4f | %5.4f | %11.4f | %9.4f  (violations %d)\n', ...
    r,ba,bn,tr,f1,f2,bad);
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
