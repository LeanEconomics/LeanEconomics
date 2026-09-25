% Bound Var_w(u), u = M/C, through the MPC rather than through levels.
% Across income states at fixed assets b, cash on hand differs by y(z')-y(z''), so
%     kap_k |dy| <= |C(z') - C(z'')| <= s |dy|      with s an upper bound on the propensity.
% Worst case over admissible C: put C(z') = Cref + s (y(z') - yref), Cref >= the incidence floor.
% Reports the critical s at which the worst-case Var meets the allowance.
function varmpc
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; gam=1;
[Pi,y,nu]=tauchen(rho,sigma,nz);
na=400; ag=[0; exp(linspace(log(1e-3),log(2000),na-1))'];
R1=1.04; q=(R1/1.06)^(1/gam); Th1=(beta*R1)^(1/gam);
kap=zeros(J,1); kap(1)=1;
for k=1:J-1, kap(k+1)=kap(k)*R1/(Th1+kap(k)*R1); end
Hr=zeros(nz,J);
for k=1:J-1
  x=y+Hr(:,k); pm=zeros(nz,1);
  for z=1:nz, w=Pi(z,:)'; pm(z)=1/(w'*(1./x)); end
  Hr(:,k+1)=min(pm/R1,(1/kap(k+1)-1)*y);
end
c1f=egm(R1,beta,gam,y,Pi,ag,J); m1=y'+R1*ag;
fprintf(' stage | allowance | Var true | true MPC | s=1 (trivial) | critical s | needed slope bound\n');
for k=[J-1 40 20]
  allow=Th1/(q*(1-kap(k+1)*R1))-1;
  Vt=0; V1=0; scrit=inf; mpct=0;
  for z=1:nz
    b1=max(m1(:,z)-c1f{k+1}(:,z),0);
    for i=1:6:na
      b=b1(i); if b<=0, continue; end
      Cn=zeros(nz,1);
      for zp=1:nz, Cn(zp)=interp1(ag,c1f{k}(:,zp),b,'linear','extrap'); end
      w=Pi(z,:)'; M=1/(w'*(1./Cn)); Vt=max(Vt,w'*((M./Cn).^2)-1);
      % true cross-state slope of C in y
      mpct=max(mpct,max(diff(Cn)./diff(y)));
      Cfl=kap(k+1)*(y(1)+R1*b+Hr(1,k+1));         % floor at the lowest income state
      yref=w'*y;
      f=@(s) varof(s,y,yref,w,Cfl,z);
      V1=max(V1,f(1));
      % critical s by bisection
      lo=0; hi=1;
      if f(hi)<=allow, sc=hi; else
        for it=1:40, mid=(lo+hi)/2; if f(mid)<=allow, lo=mid; else, hi=mid; end, end
        sc=lo;
      end
      scrit=min(scrit,sc);
    end
  end
  fprintf(' %5d | %9.4f | %8.4f | %8.4f | %13.3f | %10.4f | %s\n',...
          k,allow,Vt,mpct,V1,scrit,tick(scrit));
end
fprintf('\n a proved upper bound on the propensity below the critical s closes gamma=1.\n');
end
function s=tick(sc), if sc>=1, s='trivial MPC<=1 suffices'; else, s=sprintf('need MPC <= %.3f',sc); end, end
function V=varof(s,y,yref,w,Cfl,z)
C=Cfl+s*(y-y(1));                 % worst admissible profile anchored at the floor
C=max(C,1e-8);
M=1/(w'*(1./C));
V=w'*((M./C).^2)-1;
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
