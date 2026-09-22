% Is the risk correction a BORROWING-CONSTRAINT effect? Loosen the limit and watch the threshold.
% If the constraint is the channel, the risky threshold should walk back to the certainty-
% equivalent one (4.33) as the limit loosens; if it stays put, the channel is precaution.
function borrow
beta=0.96; J=60; R=1.04; nz=7; rho=0.9; sigma=0.4;
[y,Pi]=tauchen(rho,sigma,nz);
e=zeros(nz,1); e(nz)=1; ypath=zeros(J,1); v=e;
for t=1:J, ypath(t)=v'*y; v=Pi'*v; end
gce=critCE(ypath,beta,R,J);
fprintf('certainty-equivalent threshold  gamma_CE = %.3f   (1/gamma = %.4f)\n',gce,1/gce);
fprintf('natural borrowing limit  y_min/r = %.3f\n\n',min(y)/(R-1));
fprintf('  limit phi | gamma_risky | 1/gamma | gap in 1/gamma | share of gap closed\n');
g0=[];
for phi=[0 0.5 1 2 3 4 5 6]
  g=critRisky(y,Pi,beta,R,J,phi);
  if isempty(g0), g0=g; end
  d=1/g-1/gce; d0=1/g0-1/gce;
  fprintf(' %10.2f | %11.3f | %7.4f | %14.4f | %16.1f%%\n',phi,g,1/g,d,100*(1-d/d0));
end
% how often is the constraint binding, at gamma=3, phi=0?
gam=3; ag=grid(0); c=egm(R,beta,gam,y,Pi,ag,J,0);
fprintf('\nat gamma=3, phi=0: share of (stage,state) grid points at the corner, by stage:\n');
for k=[1 5 10 20 40 59]
  m=y'+R*ag; ap=m-c{k+1}; fprintf('  k=%2d: %.1f%%\n',k,100*mean(ap(:)<1e-9));
end
end
function ag=grid(phi)
ag=[-phi+[0; exp(linspace(log(1e-4),log(800),2499))']];
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
lo=1; hi=200;
for i=1:80
  g=(lo+hi)/2; w=beta.^(t/g).*R.^(t/g-t); Tc=sum(t.*w)/sum(w);
  if -Ty+(1-1/g)*Tc < 0, lo=g; else hi=g; end
end
g=lo;
end
function g=critRisky(y,Pi,beta,R,J,phi)
nz=numel(y); ag=grid(phi); lo=1; hi=60; dr=1e-4; i0=find(ag>=0,1);
for i=1:28
  g=(lo+hi)/2;
  c1=egm(R,beta,g,y,Pi,ag,J,phi); c2=egm(R+dr,beta,g,y,Pi,ag,J,phi);
  d=(y(nz)-c2{J}(i0,nz))-(y(nz)-c1{J}(i0,nz));
  if d>0, lo=g; else hi=g; end
end
g=lo;
end
function c=egm(R,beta,gamma,y,Pi,ag,J,phi)
nz=numel(y); na=numel(ag); m=y'+R*ag; c=cell(J,1); c{1}=m+phi;   % last period: consume down to -phi
for k=1:J-1
  up=c{k}.^(-gamma); rhs=beta*R*(up*Pi'); cend=rhs.^(-1/gamma); mend=cend+ag; cn=zeros(na,nz);
  for z=1:nz
    cn(:,z)=interp1(mend(:,z),cend(:,z),m(:,z),'linear','extrap');
    corner=m(:,z)<mend(1,z); cn(corner,z)=m(corner,z)+phi;       % pinned at the limit
  end
  cn=min(cn,m+phi); cn=max(cn,1e-12); c{k+1}=cn;
end
end
