% How big is the gap between the risky and certainty-equivalent thresholds, and what does it
% scale with? Both thresholds are measured at the same state: zero wealth, top earnings, first
% period of a J-period life. CE threshold from the exact duration criterion; risky threshold by
% bisection on the sign of d(saving)/dr.
function gapscale
beta=0.96; J=60; R=1.04; nz=7;
fprintf('  rho |  sigma | var(log y) | gamma_CE | gamma_risky |  gap  | gap/var\n');
for rho=[0.6 0.9]
  for sigma=[0.1 0.2 0.3 0.4 0.5 0.6]
    [y,Pi]=tauchen(rho,sigma,nz);
    e=zeros(nz,1); e(nz)=1; ypath=zeros(J,1); v=e;
    for t=1:J, ypath(t)=v'*y; v=Pi'*v; end
    gce=critCE(ypath,beta,R,J);
    gr =critRisky(y,Pi,beta,R,J);
    fprintf(' %.2f | %6.2f | %10.4f | %8.3f | %11.3f | %5.3f | %7.3f\n',...
      rho,sigma,sigma^2,gce,gr,gce-gr,(gce-gr)/sigma^2);
  end
end
end
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
t=(0:J-1)'; W=sum(ypath.*R.^(-t)); Ty=sum(t.*ypath.*R.^(-t))/W;
lo=1; hi=40;
for i=1:60
  g=(lo+hi)/2; w=beta.^(t/g).*R.^(t/g-t); Tc=sum(t.*w)/sum(w);
  if -Ty+(1-1/g)*Tc < 0, lo=g; else hi=g; end
end
g=lo;
end
function g=critRisky(y,Pi,beta,R,J)
nz=numel(y); ag=[0; exp(linspace(log(1e-4),log(800),2499))'];
lo=1; hi=40; dr=1e-4;
for i=1:26
  g=(lo+hi)/2;
  c1=egm(R,beta,g,y,Pi,ag,J); c2=egm(R+dr,beta,g,y,Pi,ag,J);
  d=(y(nz)-c2{J}(1,nz))-(y(nz)-c1{J}(1,nz));
  if d>0, lo=g; else hi=g; end
end
g=lo;
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
