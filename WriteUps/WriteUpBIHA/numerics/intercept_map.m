% The intercept map of the rate-response induction (Section "What remains").
% Run rate_response_check(outdir) first; this loads outdir/rate_response.mat.
% For each income state z the map sends an intercept vector B to the smallest intercept that the
% transfer step (exact Euler weighting over tomorrow's income) delivers at state z when tomorrow's
% gap is bounded by dr*(alpha a' + B_{z'}). Prints the iteration, the Jacobian at B=0 and its
% spectral radius. Row sums >= 1/Thorn_1 > 1 by the Euler equation and the power-mean inequality.
function intercept_map(outdir)
load(fullfile(outdir,'rate_response.mat'),'ag','c1','c2','ap1','ap2','gap','Pi');
gamma=3; beta=0.96; r1=0.040; r2=0.041; R1=1+r1; R2=1+r2; dr=r2-r1; nz=size(c1,2); na=numel(ag);
kappa1=1-(beta*R1)^(1/gamma)/R1; alpha0=1-(1-kappa1)/gamma;
c1a1=cell(nz,1); c1a2=cell(nz,1);
for z=1:nz, c1a1{z}=zeros(na,nz); c1a2{z}=zeros(na,nz);
  for zz=1:nz
    c1a1{z}(:,zz)=interp1(ag,c1(:,zz),ap1(:,z),'linear','extrap');
    c1a2{z}(:,zz)=interp1(ag,c1(:,zz),ap2(:,z),'linear','extrap');
  end
end
fprintf('true gap (c2-c1)/dr at a=0 by z: %s\n',mat2str(gap(1,:),3));
fprintf('c1 at a=0 by z: %s ; SEC tolerance at a=0 c1/(gamma R1): %s\n',mat2str(c1(1,:),3),mat2str(c1(1,:)/(gamma*R1),3));
for al=[alpha0 0.73 0.80 1.0]
  fprintf('alpha=%.3f: max_a (gap - alpha a) by z = %s\n',al,mat2str(max(gap-al*ag,[],1),2));
end
T=@(B,al) tmap(B,al,c1,c1a1,c1a2,ap1,ap2,ag,Pi,dr,R1,R2,gamma,nz);
for al=[alpha0+0.05 alpha0+0.12]
  B=max(gap-al*ag,[],1); fprintf('\nalpha=%.3f, iterating B <- T(B)\n',al);
  for it=1:400
    [Bnew,worst]=T(B,al);
    if mod(it,50)==0, fprintf('  it %3d: B=%s binding a=%s max step %.2e\n',it,mat2str(Bnew,3),mat2str(worst,3),max(abs(Bnew-B))); end
    B=Bnew;
  end
end
al=alpha0+0.05; B0=zeros(1,nz); h=0.05; [T0,w0]=T(B0,al);
fprintf('\nT(0) at alpha=%.3f = %s, binding a = %s\n',al,mat2str(T0,3),mat2str(w0,3));
J=zeros(nz);
for j=1:nz, Bp=B0; Bp(j)=h; Tp=T(Bp,al); J(:,j)=(Tp-T0)'/h; end
disp('Jacobian dT_z/dB_zprime at B=0 (rows z):'); disp(round(J,3));
fprintf('row sums: %s  spectral radius: %.4f  1/Thorn1 = %.5f\n',mat2str(sum(J,2)',3),max(abs(eig(J))),(beta*R1)^(-1/gamma));
end

function [Bnew,worst]=tmap(B,al,c1,c1a1,c1a2,ap1,ap2,ag,Pi,dr,R1,R2,gamma,nz)
Bnew=zeros(1,nz); worst=zeros(1,nz);
for z=1:nz
  X=(c1a2{z}-c1a1{z})+dr*(al*ap2(:,z)+B); X=max(X,0);
  pz=Pi(z,:); Eu=(c1a1{z}.^(-gamma))*pz'; EuX=((c1a1{z}+X).^(-gamma))*pz';
  cb=(R1/R2)^(1/gamma)*c1(:,z).*(Eu./EuX).^(1/gamma);
  int=ap1(:,z)>1e-9; need=(cb-c1(:,z))/dr-al*ag; need(~int)=-inf;
  [Bnew(z),k]=max(need); worst(z)=ag(k);
end
end
