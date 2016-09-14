class AdminController < ApplicationController
  before_action  :kick_out_unauthorized?

  # use this to kick out unauthorized profiles
  def kick_out_unauthorized?
    @unauthorized_allowed_actions = ['signup', 'login']
    
    if @unauthorized_allowed_actions.include?(params[:action]) then
      return
    end


    if not session.has_key?("admin_id") then
      redirect_to :controller => 'admin', :action => 'login'
    end
  end

  # Use this to automatically redirect to an authorized page
  def auto_redirect_authorized?
    if session.has_key?("admin_id") then
      redirect_to_action = "mainpage"
      if params.has_key?(:redirect_to) then
        redirect_to_action = params[:redirect_to]
      end
      redirect_to :controller => 'admin', :action => redirect_to_action
    end

  end
  

  def logout
    session[:admin_id] = nil
    redirect_to :controller => 'admin', :action => 'login'
  end

  
  def login
    if auto_redirect_authorized? then
      return
    end

   if not request.post? then
        return
    end

 
    @admin = Admin.find_by(username: user_params[:username])

    if @admin.nil? then
      flash[:error] = {"username": ['does not exist']}
      redirect_to :controller => 'admin', :action => 'login'
    
    elsif !@admin.authenticate(user_params[:password]) then
      flash[:error] = {"password": ["maybe incorrect"], "username": ["maybe incorrect"]}
      redirect_to :controller => 'admin', :action => 'login'
    else
      session["admin_id"] = @admin.id
      # TODO: allow custom redirects here
      redirect_to :controller => 'admin', :action => 'mainpage'
    end
  end

  def user_params
    params.require(:user).permit(:name, :email, :username, :password, :password_conformation)
  end

end
