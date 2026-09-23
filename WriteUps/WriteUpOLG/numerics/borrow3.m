% Fair cross-calibration check: loosen the limit to a MODERATE fraction of the natural one and
% ask what fraction of the threshold gap closes. Avoids the very-high-risk-aversion region where
% the numerics are unreliable.
function borrow3
beta=0.96; J=60; R=1.04; nz=7;
fprintf('  rho | sigma | nat=y_min/r | gamma_CE | phi/nat | gamma_risky | gap closed\n');
for rho=[0.9 0.6]
  for sigma=[0.2 0.4]
    [y,Pi]=tauchen(rho,sigma,nz);
    e=zeros(nz,1); e(nz)=1; ypath=zeros(J,1); v=e;
    for t=1:J, ypath(t)=v'*y; v=Pi'*v; end
    gce=critCE(ypath,beta,R,J); nat=min(y)/(R-1);
    g0=critRisky(y,Pi,beta,R,J,0); d0=1/g0-1/gce;
    for f=[0.25 0.5]
      g=critRisky(y,Pi,beta,R,J,f*nat); d=1/g-1/gce;
      fprintf(' %.2f | %5.2f | %11.3f | %8.3f | %7.2f | %11.3f | %8.1f%%\n',...
        rho,sigma,nat,gce,f,g,100*(1-d/d0));
    end
  end
end
end
function ag=grid(phi), ag=[-phi+[0; exp(linspace(log(1e-4),log(800),2999))']]; end
function [y,Pi]=tauchen(rho,sigma,nz)
sd_e=sigma*sqrt(1-rho^2); xg=linspace(-3*sigma,3*sigma,nz); h=xg(2)-xg(1);
Pi=zeros(nz); for i=1:nz, for j=1:nz
  lo=(xg(j)-h/2-rho*xg(i))/sd_e; hi=(xg(j)+h/2-rho*xg(i))/sd_e;
  if j==1, Pi(i,j)=Phi(hi); elseif j==nz, Pi(i,j)=1-Phi(lo); else Pi(i,j)=Phi(hi)-Phi(lo); end
end, end
[V,D]=eig(Pi'); [~,k]=max(abs(diag(D))); p=abs(V(:,k)); p=p/sum(p); y=exp(xg)'; y=y/(p'*y);
end
function v=Phi(x), v=0.5*erfc(-x/sqrt(2)); end
function g=critCE(ypath,beta,R,J)
t=(0:J-1)'; W=sum(ypath.*R.^(-t)); Ty=sum(t.*ypath.*R.^(-t))/W; lo=1; hi=200;
for i=1:80
  g=(lo+hi)/2; w=beta.^(t/g).*R.^(t/g-t); Tc=sum(t.*w)/sum(w);
  if -Ty+(1-1/g)*Tc < 0, lo=g; else hi=g; end
end
g=lo;
end
function g=critRisky(y,Pi,beta,R,J,phi)
ag=grid(phi); lo=1; hi=40; dr=1e-4; i0=find(ag>=0,1);
for i=1:26
  g=(lo+hi)/2;
  c1=egm(R,beta,g,y,Pi,ag,J,phi); c2=egm(R+dr,beta,g,y,Pi,ag,J,phi);
  if (y(end)-c2{J}(i0,end))-(y(end)-c1{J}(i0,end))>0, lo=g; else hi=g; end
end
g=lo;
end
function c=egm(R,beta,gamma,y,Pi,ag,J,phi)
nz=numel(y); na=numel(ag); m=y'+R*ag; c=cell(J,1); c{1}=m+phi;
for k=1:J-1
  up=c{k}.^(-gamma); rhs=beta*R*(up*Pi'); cend=rhs.^(-1/gamma); mend=cend+ag; cn=zeros(na,nz);
  for z=1:nz
    cn(:,z)=interp1(mend(:,z),cend(:,z),m(:,z),'linear','extrap');
    corner=m(:,z)<mend(1,z); cn(corner,z)=m(corner,z)+phi;
  end
  cn=min(cn,m+phi); cn=max(cn,1e-12); c{k+1}=cn;
end
end
