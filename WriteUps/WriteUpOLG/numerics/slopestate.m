% State-dependent slope.  The saving floor of LowerSandwich says the constraint cannot bind at
% (b,z') whenever  (1-kap_k)(y(z') + R b) > kap_k H_k(z')  -- a primitive test.  Where it does not
% bind the Euler holds and the cross-state slope of C is small; where it binds C = cash on hand and
% the slope is 1.  Question: at the b's that actually arise, does the constraint bind at all?
function slopestate
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; gam=1;
[Pi,y,nu]=tauchen(rho,sigma,nz);
na=400; ag=[0; exp(linspace(log(1e-3),log(2000),na-1))'];
R1=1.04; q=(R1/1.06)^(1/gam); Th1=(beta*R1)^(1/gam);
kap=zeros(J,1); kap(1)=1;
for k=1:J-1, kap(k+1)=kap(k)*R1/(Th1+kap(k)*R1); end
Ha=zeros(nz,J);
for k=1:J-1, Ha(:,k+1)=(Pi*(y+Ha(:,k)))/R1; end
c1f=egm(R1,beta,gam,y,Pi,ag,J); m1=y'+R1*ag;
fprintf(' stage | allow | true slope max | constrained (true) | floor test certifies unconstrained\n');
for k=[J-1 40 20 5]
  allow=Th1/(q*(1-kap(k+1)*R1))-1;
  smax=0; nb=0; ntot=0; ncert=0; wbad=0;
  for z=1:nz
    b1=max(m1(:,z)-c1f{k+1}(:,z),0);
    for i=1:12:na
      b=b1(i); if b<=0, continue; end
      Cn=zeros(nz,1); Pn=zeros(nz,1);
      for zp=1:nz
        Cn(zp)=interp1(ag,c1f{k}(:,zp),b,'linear','extrap');
        Pn(zp)=max(0,(y(zp)+R1*b)-Cn(zp));
      end
      smax=max(smax,max(diff(Cn)./diff(y)));
      w=Pi(z,:)';
      bind=Pn<1e-9; ntot=ntot+nz; nb=nb+sum(bind);
      wbad=max(wbad,sum(w(bind)));
      cert=(1-kap(k+1))*(y+R1*b) > kap(k+1)*Ha(:,k+1);
      ncert=ncert+sum(cert);
    end
  end
  fprintf(' %5d | %.3f | %14.4f | %7.1f%% of states | %10.1f%% certified ; worst bound mass %.2e\n',...
          k,allow,smax,100*nb/ntot,100*ncert/ntot,wbad);
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
