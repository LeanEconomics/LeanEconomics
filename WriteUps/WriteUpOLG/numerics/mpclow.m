% Is the MPC out of cash-on-hand at least kap_k?  (needed for saving Lipschitz with (1-kap_k)R)
function mpclow
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60;
[Pi,y,nu]=tauchen(rho,sigma,nz);
na=500; ag=[0; exp(linspace(log(1e-3),log(4000),na-1))'];
fprintf(' gam    r   | worst (dc/dm - kap_k) over reached states | stages failing | worst kap\n');
for gam=[1 2 3 5 8]
  for r=[0.04 0.06]
    R=1+r; Th=(beta*R)^(1/gam);
    kap=zeros(J,1); kap(1)=1; for k=1:J-1, kap(k+1)=kap(k)*R/(Th+kap(k)*R); end
    c=egm(R,beta,gam,y,Pi,ag,J); m=y'+R*ag;
    worst=inf; nf=0; wk=0;
    for k=0:J-1
      bad=false;
      for z=1:nz
        cc=c{k+1}(:,z); mm=m(:,z);
        d=diff(cc)./diff(mm);
        g=min(d)-kap(k+1);
        if g<worst, worst=g; wk=k; end
        if g<-1e-8, bad=true; end
      end
      if bad, nf=nf+1; end
    end
    fprintf(' %3g %.3f | %+38.2e | %8d of %d | k=%d\n',gam,r,worst,nf,J,wk);
  end
end
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
