% Why the quantitative step fails, and whether a direct (non-inductive) bound could replace it.
%  (i)  per-step amplification of the eps recursion: d(Dbnd)/d(eps_k) = c1 * q / C1_min(worst z')
%  (ii) the direct sandwich bound on the failure D = c2 - c1 - dr*a, which needs no induction:
%         c2 <= kap2_{k+1}(m2 + H2_{k+1}),  c1 >= kap1_{k+1} m1
function vjdiag
beta=0.96; rho=0.9; sigma=0.4; nz=7; J=60; alpha=9/25; delta=2/25;
[Pi,y,nu]=tauchen(rho,sigma,nz); D=@(r) alpha/((1-alpha)*(r+delta));
na=400; ag=[0; exp(linspace(log(1e-3),log(2000),na-1))'];
r1=0.04; r2=0.06; R1=1+r1; R2=1+r2; dr=r2-r1;
budget=D(r1)-D(r2);
fprintf('budget %.4f ; per-age nu-weighted allowance ~ %.4f (accumulation ~21)\n\n',budget,budget/21);
for gam=[5 8]
  q=(R1/R2)^(1/gam);
  c1f=egm(R1,beta,gam,y,Pi,ag,J); c2f=egm(R2,beta,gam,y,Pi,ag,J);
  m1=y'+R1*ag; m2=y'+R2*ag;
  k1=mpc(R1,beta,gam,J); k2=mpc(R2,beta,gam,J);
  H1=hw(Pi,y,R1,J); H2=hw(Pi,y,R2,J);
  % (i) amplification
  amp=0;
  for k=1:J-1
    for z=1:nz
      b1=max(m1(:,z)-c1f{k+1}(:,z),0); c1=c1f{k+1}(:,z);
      for i=1:na
        if b1(i)<=0, continue; end
        Cn=zeros(nz,1);
        for zp=1:nz, Cn(zp)=interp1(ag,c1f{k}(:,zp),b1(i),'linear','extrap'); end
        amp=max(amp,c1(i)*q/min(Cn));
      end
    end
  end
  % (ii) direct sandwich bound
  ds=0; dst=0;
  for k=0:J-1
    for z=1:nz
      v=k2(k+1)*(m2(:,z)+H2(z,k+1))-k1(k+1)*m1(:,z)-dr*ag;
      ds=max(ds,max(v));
      vt=max(0,(m1(:,z)-c1f{k+1}(:,z))-(m2(:,z)-c2f{k+1}(:,z)));
      dst=max(dst,max(vt));
    end
  end
  fprintf(' gamma=%g : per-step amplification of eps  = %8.1f   (needs <= 1 to not explode)\n',gam,amp);
  fprintf('           direct sandwich bound on failure = %8.4f   (true sup %.4f, allowance %.4f)\n',...
          ds,dst,budget/21);
  fprintf('           max_k kap_k * mean H_k            = %8.4f\n',max(k1'.*(nu'*H1)));
end
end
function k=mpc(R,beta,gam,J)
Th=(beta*R)^(1/gam); k=zeros(J,1); k(1)=1;
for j=1:J-1, k(j+1)=k(j)*R/(Th+k(j)*R); end
end
function H=hw(Pi,y,R,J)
nz=numel(y); H=zeros(nz,J); for k=1:J-1, H(:,k+1)=(Pi*(y+H(:,k)))/R; end
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
