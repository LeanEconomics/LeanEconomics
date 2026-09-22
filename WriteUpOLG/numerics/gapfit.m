% The criterion in IES units: CE says  1/gamma >= 1 - T_y/T_c.  With risk the threshold moves by
% Delta = 1/gamma_risky - 1/gamma_CE.  How does Delta scale with the conditional risk?
function gapfit
beta=0.96; J=60; R=1.04; nz=7;
fprintf('  rho |  sigma | cond sd s=sigma*sqrt(1-rho^2) | 1/g_CE  | 1/g_risky |  Delta  | Delta/s | Delta/s^2\n');
res=[];
for rho=[0.9 0.6 0.0]
  for sigma=[0.025 0.05 0.1 0.2 0.4]
    [y,Pi]=tauchen(rho,sigma,nz);
    e=zeros(nz,1); e(nz)=1; ypath=zeros(J,1); v=e;
    for t=1:J, ypath(t)=v'*y; v=Pi'*v; end
    gce=critCE(ypath,beta,R,J); gr=critRisky(y,Pi,beta,R,J);
    s=sigma*sqrt(1-rho^2); D=1/gr-1/gce;
    fprintf(' %.2f | %6.3f | %28.4f | %7.4f | %9.4f | %7.4f | %7.3f | %9.2f\n',...
      rho,sigma,s,1/gce,1/gr,D,D/s,D/s^2);
    res(end+1,:)=[rho sigma s D];
  end
end
% fit log Delta = a + b log s within each rho
fprintf('\n fitted exponent b in Delta ~ s^b (by rho):\n');
for rho=[0.9 0.6 0.0]
  m=res(res(:,1)==rho,:); b=polyfit(log(m(:,3)),log(m(:,4)),1);
  fprintf('   rho=%.2f : b = %.3f,  Delta ~ %.3f * s^%.3f\n',rho,b(1),exp(b(2)),b(1));
end
end
function [y,Pi]=tauchen(rho,sigma,nz)
if rho==0, sd_e=sigma; else sd_e=sigma*sqrt(1-rho^2); end
xg=linspace(-3*sigma,3*sigma,nz); h=xg(2)-xg(1);
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
function g=critRisky(y,Pi,beta,R,J)
nz=numel(y); ag=[0; exp(linspace(log(1e-4),log(800),2499))'];
lo=1; hi=200; dr=1e-4;
for i=1:30
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
